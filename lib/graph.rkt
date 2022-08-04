#lang racket
(require
  (prefix-in r: rosette/safe)
  racket/random
  racket/stxparam
  [except-in "../private/problem-definition-core.rkt" max min]
  [for-syntax racket/syntax
              racket/struct
              syntax/parse
              racket/match
              racket/syntax-srcloc]
  [for-meta 2 racket/base
              syntax/parse]
  "../private/karp-contract.rkt")

;; GRAPH
;; data defintion: a graph is a hash from symbols to lists of symbols
;; interpretation: the domain of the hash is the set of nodes of the
;;                 the graph, the hash maps each node x to a list of
;;                 y... such that (x, y_i) is an edge in the graph
;;                 for all y_i in y...,
;; invarinant:     if y maps to x... that contains x then x maps to y..
;;                 contains y

(provide

 (struct-out dp-graph)
 
 -e-
 -e->
 has-edge?
 has-edge?-u-safe
 has-edge?-v-safe
 has-edge?-uv-safe
 vertex/c
 edge-u/c

 ;make-edge
 e-u
 e-u-u
 e-u-d
 e-v
 e-v-u
 e-v-d
 incident?
 incident?-u-safe
 endpoints
 
 dp-graph-V-M?
 dp-graph/c
 subgraph-of?
 dp-graph-u-invariant?
 dp-graph-u/c
 dp-graph-d/c
 dp-graph-u/kc
 dp-graph-d/kc
 empty-graph
 get-vertices
 get-edges

 dp-graph-V-size=-d/kc
 dp-graph-E-size=-d/kc
 
 neighbors
 in-neighbors
 
 create-graph
 create-graph-from-edges

 dp-symbolic-subgraph
 dp-symbolic-path
 dp-graph-from-sol
 ; temp provide
 dp-underlying-u-graph
 dp-r-path-constraint
 dp-r-connected
 dp-r-st-reachable
 dp-r-st-test
 dp-r-test
 dp-r-acyclic
 dp-graph-V-ground
 ; end

 ; create graph out of graph
 remove-edge
 remove-edges
 remove-vertices

 connected?
 reachable?
 acyclic?
 st-path?
 
 dp-dfs-pre

 generate-random-graph-sample-edge

 graph
 vertex-of
 vertices-of
 edges-of
 subgraph-of
 path
 )

; type objects representing CNF, clauses and literals
(begin-for-syntax
  ; why export the binding (assuming nothing on top of the graph lib)
  #;(provide tGraph
             tEdge)

  (struct ty-Graph (directed?)
    #:transparent
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) (if (ty-Graph-directed? self)
                      'DirectedGraph
                      'UndirectedGraph))
        (λ (self) '())))])

  (struct ty-Edge (directed?)
    #:transparent
    #:property prop:type-interface
    (list (cons 'set (λ (self)
                       (if (ty-Edge-directed? self)
                           (tTuple (tSymbol) (tSymbol))
                           (tSetOf (tSymbol))))))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) (if (ty-Edge-directed? self)
                      'DirectedEdge
                      'UndirectedEdge))
        (λ (self) '())))])
  
  (define-match-expander tUGraph
    (syntax-parser
      [(_) #'(ty-Graph #f)])
    (syntax-parser
      [(_) #'(ty-Graph #f)]))

  (define-match-expander tDGraph
    (syntax-parser
      [(_) #'(ty-Graph #t)])
    (syntax-parser
      [(_) #'(ty-Graph #t)]))

  (define-match-expander tGraph
    (syntax-parser
      [(_ directed?) #'(ty-Graph directed?)])
    (syntax-parser
      [(_ directed?) #'(ty-Graph directed?)]))

  (define-match-expander tEdge
    (syntax-parser
      [(_ directed?) #'(ty-Edge directed?)])
    (syntax-parser
      [(_ directed?) #'(ty-Edge directed?)]))

  (define-match-expander tUEdge
    (syntax-parser
      [(_) #'(ty-Edge #f)])
    (syntax-parser
      [(_) #'(ty-Edge #f)]))

  (define-match-expander tDEdge
    (syntax-parser
      [(_) #'(ty-Edge #t)])
    (syntax-parser
      [(_) #'(ty-Edge #t)]))
)


; M: (hash/c (hash/c any/c any/c) boolean?) -- adjacency matrix
; V: dp-set/c
; XXX: No custom equal? at this time
;      fallback to Racket in the future, see also : dp-set
; XXX: should fallback to Racket struct instead of using r:struct?
(r:struct dp-graph (M V directed?) #:transparent
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (a-graph port mode)
                 (fprintf port "[graph\n~a\n]"
                          (string-join
                           (map
                            (λ (v)
                              (format "  ~a : ~a" v
                                      (dp-set (hash-ref (dp-graph-M a-graph) v))))
                            (dp-set-members->list (dp-graph-V a-graph))) "\n"))))])

; get the ground set (as list) of the vertices of g
; internal
(define (dp-graph-V-ground g)
  (hash-keys (dp-set-S (dp-graph-V g))))

; invariant: all vertices in V are in hash-key of M
(define (dp-graph-V-M? g)
  (r:and
   (r:andmap
    (r:λ (v)
         (r:implies
          (set-∈ v (dp-graph-V g))
          (hash-ref (dp-graph-M g) v #f)))
    (dp-graph-V-ground g))
   (r:andmap
    (r:λ (u)
         (r:andmap
          (r:λ (v)
               (r:implies
                (hash-ref (hash-ref (dp-graph-M g) u) v #f)
                (r:and
                 (set-∈ u (dp-graph-V g))
                 (set-∈ v (dp-graph-V g)))))
          (hash-keys (hash-ref (dp-graph-M g) u))))
    (hash-keys (dp-graph-M g)))))

(define dp-graph/c
  (and/c
   (struct/c dp-graph
             (hash/c
              any/c
              (hash/c any/c any/c #:immutable #t #:flat? #t)
              #:immutable #t #:flat? #t)
             dp-set/c
             boolean?)
   dp-graph-V-M?))

(define dp-graph/kc
  (and/kc
    (make-simple-contract/kc (v)
       (dp-graph? v)
       "expects a graph")
    (make-simple-contract/kc (v)
       ((struct/c dp-graph
          (hash/c
           any/c
           (hash/c any/c any/c #:immutable #t #:flat? #t)
           #:immutable #t #:flat? #t)
          dp-set/c
          boolean?) v)
       "internal error: invalid graph structure")
     (make-simple-contract/kc (v)
       (dp-graph-V-M? v)
       "invalid graph: exists vertex with no corresponding row in adjancency matrix")))

; invariant for undirected graph
(define (dp-graph-u-invariant? g)
  (r:let ([adj-m (dp-graph-M g)])
         (r:andmap
          (r:λ (u)
               (r:implies
                (set-∈ u (dp-graph-V g))
                (r:andmap
                 (r:λ (v)
                      (r:implies
                       (hash-ref (hash-ref adj-m u) v #f)
                       (hash-ref (hash-ref adj-m v) u #f)))
                 (hash-keys (hash-ref adj-m u)))))
          (dp-graph-V-ground g))))

(define-simple-contract/kc dp-graph-u-invariant/kc (v)
  (dp-graph-u-invariant? v)
  "invalid undirected graph: adjancency matrix is asymmetric")

; contract for undirected graph
(define dp-graph-u/c
  (and/c
   dp-graph/c
   dp-graph-u-invariant?
   (λ (g) (not (dp-graph-directed? g)))))

(define dp-graph-u/kc
  (and/kc
   (make-simple-contract/kc (g)
    (dp-graph? g)
    "expects an undirected graph")
   dp-graph/kc
   (make-simple-contract/kc (g)
    (not (dp-graph-directed? g))
    "expects an undirected graph, but a directed one is given")
   dp-graph-u-invariant/kc))

; contract for directed graph
(define dp-graph-d/c
  (and/c
   dp-graph/c
   (λ (g) (dp-graph-directed? g))))

(define dp-graph-d/kc
  (and/kc
   (make-simple-contract/kc (g)
    (not (dp-graph? g))
    "expects a directed graph")
   dp-graph/kc
   (make-simple-contract/kc (v)
     (dp-graph-directed? v)
     "expects an directed graph, but an undirected is given")))

(define (subgraph-of? g1 g2)
  (r:and
   (r:equal? (dp-graph-directed? g1) (dp-graph-directed? g2))
   (set-subset-of? (dp-graph-V g1) (dp-graph-V g2))
   (r:andmap
    (r:λ (u)
         (r:implies
          (set-∈ u (dp-graph-V g1))
          (r:andmap
           (r:λ (v)
                (r:implies
                 (hash-ref (hash-ref (dp-graph-M g1) u) v #f)
                 (hash-ref (hash-ref (dp-graph-M g2) u) v #f)))
           (hash-keys (hash-ref (dp-graph-M g1) u)))))
    (dp-graph-V-ground g1))))
(kv-func-type-annotate subgraph-of? ((tGraph dir?) (tGraph dir?) (tBool))
                                    "two graphs")

(define (subgraph-of-d/kc g)
  (make-simple-contract/kc (g2)
    (subgraph-of? g2 g)
    (format "expects a subgraph of ~e" g)))

#;(define-syntax (make-edge stx)
  (syntax-parse stx
    [(_ p ) #'(edge-u p)]
    [(_ u v) #'(edge-u (r:cons u v))]))

(define vertex/c any/c)
(provide edge-u/kc edge-d/kc)
;(define edge-u/c (struct/c edge-u (cons/c vertex/c vertex/c)))
(define edge-u/c (and/c
                  (dp-setof/c vertex/c)
                  (λ (e) (<= (set-size e) 2))))
(define-simple-contract/kc edge-u/kc (v)
  ((and/kc
    dp-set/kc
    (dp-set-with-size=/kc 2))
   v #f 'as-predicate '()
   #t) ; predicate?
  "expects an undirected edge (a set of size 2)")
;(define edge/c (cons/c vertex/c vertex/c))

(define-simple-contract/kc edge-d/kc (v)
  ((dp-duple-with-length=/kc 2)
   v #f 'as-predicate '()
   #t) ; predicate?
  "expects an directed edge (a tuple of 2 components)")


(provide has-edge?-typed-rewriter)
(define-syntax has-edge?-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON (tSymbol)) ('CON (tSymbol)) (_ (tGraph _)))
       (λ (stx) (cons stx (tBool)))]
      [(args-τ ('SYM (tSymbol)) ('CON (tSymbol)) (_ (tGraph _)))
       (syntax-parser
           [(has-edge? u v g) (cons #'(has-edge?-u-safe u v g) (tBool))])]
      [(args-τ ('CON (tSymbol)) ('SYM (tSymbol)) (_ (tGraph _)))
       (syntax-parser
           [(has-edge? u v g) (cons #'(has-edge?-v-safe u v g) (tBool))])]
      [(args-τ ('SYM (tSymbol)) ('SYM (tSymbol)) (_ (tGraph _)))
       (syntax-parser
           [(has-edge? u v g) (cons #'(has-edge?-v-safe u v g) (tBool))])]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects two vertices, gets ~a"
                                          (map get-τb type-lst))
                               stx))])))

;  possibly needs to have a version (hash-edge? e g)
(define/contract/kc (has-edge? u v g)
  (->k ([u any/kc] [v any/kc] [g dp-graph/kc]) any/kc)
  (r:if
   (r:or (set-∉ u (dp-graph-V g))
         (set-∉ v (dp-graph-V g)))
   #f
   (hash-ref (hash-ref (dp-graph-M g) u) v #f)))

(define (has-edge?-u-safe u v g)
  (r:if
   (r:or (set-∉-safe u (dp-graph-V g))
         (set-∉ v (dp-graph-V g)))
   #f
   (hash-ref (hash-ref (dp-graph-M g) u) v #f)))

(define (has-edge?-v-safe u v g)
  (r:if
   (r:or (set-∉ u (dp-graph-V g))
         (set-∉-safe v (dp-graph-V g)))
   #f
   (hash-ref (hash-ref (dp-graph-M g) u) v #f)))

(define (has-edge?-uv-safe u v g)
  (r:if
   (r:or (set-∉-safe u (dp-graph-V g))
         (set-∉-safe v (dp-graph-V g)))
   #f
   (hash-ref (hash-ref (dp-graph-M g) u) v #f)))

; old version
; does not match boolean?
#;(define (has-edge? x y g)
    (r:if
     (r:and
      (r:member y (hash-ref g x '()))
      ; was undirected
      #;(r:member x (hash-ref g y '())))
     #t
     #f))

(define/contract/kc (remove-edge g e)
  (->k ([g dp-graph/kc]
        [e (g) (case
                [(dp-graph-directed? g) edge-d/kc]
                [else edge-u/kc])])
       any/kc)
  (remove-edges g (set e)))

(define/contract/kc (remove-edges g es)
  (->k ([g dp-graph/kc]
        [e (g) (case
                [(dp-graph-directed? g) (dp-setof/kc edge-d/kc)]
                [else (dp-setof/kc edge-u/kc)])])
       any/kc)
  (r:let*
   ([directed (dp-graph-directed? g)])
   (dp-graph
    (r:foldl
     (r:λ (e adj-M)        
          (r:let
           ([u (e-u e)]
            [v (e-v e)])
           (r:let
            ([adj-M-vu
              (r:if directed
                    adj-M
                    (hash-set
                     adj-M
                     v
                     (hash-set
                      (hash-ref adj-M v)
                      u
                      (r:if
                       (set-∈ e es)
                       #f
                       (hash-ref
                        (hash-ref adj-M v)
                        u
                        #f)))))])
            (hash-set
             adj-M-vu
             u
             (hash-set
              (hash-ref adj-M-vu u)
              v
              (r:if
               (set-∈ e es)
               #f
               (hash-ref
                (hash-ref adj-M-vu u)
                v
                #f)))))))
     (dp-graph-M g)
     (dp-ground-set->list es))
    (dp-graph-V g)
    directed)))
(kv-func-type-annotate remove-edges ((tGraph dir?) (tSetOf (tEdge dir?)) (tGraph dir?))
                       "a graph and a set of edges")

; not going to work because of symbolic hash
; (r:if
;     (set-∈ e S)
;     (hash-1)
;     (hash-2))
; will resulting symbolic hash
#;(define (remove-edges g es)
  (r:let*
   ([directed (dp-graph-directed? g)]
    [edge-e (r:if directed edge-d-e edge-u-e)])
   (dp-graph
    (r:foldl
     (r:λ (e adj-M)
          (r:if
           (set-∈ e es)
           (hash-set adj-M
                     (e-u e)
                     (hash-set
                      (hash-ref adj-M (e-u e))
                      (e-v e)
                      #f))
           adj-M))
     #;(r:λ (e adj-M)
          (r:if (set-∈ e es)
                (r:let
                 ([u (r:car (edge-e e))]
                  [v (r:cdr (edge-e e))])
                 (r:if directed
                       (hash-set adj-M u (hash-set (hash-ref adj-M u) v #f))
                       (hash-set
                        (hash-set adj-M u (hash-set (hash-ref adj-M u) v #f))
                        v
                        (hash-set (hash-ref adj-M v) u #f))))
                adj-M))
     (dp-graph-M g)
     (dp-ground-set->list es))
    (dp-graph-V g)
    directed)))

(define/contract/kc (remove-vertices g vs)
  (->k ([g dp-graph/kc]
        [vs dp-set/kc])
       any/kc)
  (dp-graph
   (r:let
    ([g-M-hash (dp-graph-M g)])
    (for/hash ([u (hash-keys g-M-hash)])
      (values u
              (for/hash ([v (hash-keys (hash-ref g-M-hash u))])
                (values v (r:if
                           (r:or
                            (set-∈ u vs)
                            (set-∈ v vs))
                           #f
                           (hash-ref (hash-ref g-M-hash u) v #f)))))))
   (dp-set
    (r:foldl
     (r:λ (u V-acc)
          (hash-set V-acc u (r:if (set-∈ u vs)
                                  #f
                                  (hash-ref V-acc u #f))))
     (dp-set-S (dp-graph-V g))
     (dp-ground-set->list vs)))
   (dp-graph-directed? g)))
(kv-func-type-annotate remove-vertices ((tGraph dir?) (tSetOf (tSymbol)) (tGraph dir?))
                                       "a graph and a set of vertices")


; only works for undirected
; not in use any more as undirected edge is now set
#;(r:define (edge-equal-u? edge1 edge2 recursive-equal?)
          (r:let ([u1 (r:car (edge-u-e edge1))]
                  [v1 (r:cdr (edge-u-e edge1))]
                  [u2 (r:car (edge-u-e edge2))]
                  [v2 (r:cdr (edge-u-e edge2))])
                 (r:or (r:and
                        (recursive-equal? u1 u2)
                        (recursive-equal? v1 v2))
                       (r:and
                        (recursive-equal? u1 v2)
                        (recursive-equal? u2 v1)))))
; not in use any more as undirected edge is now set
#;(r:define (edge-hash edge recursive-equal-hash)
          (r:let ([h1 (recursive-equal-hash (edge-u-e edge))]
                  [h2 (recursive-equal-hash (r:cons (r:cdr (edge-u-e edge))
                                                    (r:car (edge-u-e edge))))])
                 (r:if (r:< h1 h2) h1 h2)))

;
; Edges of undirected graphs are now sets of size 2
; Edges of directed graphs are now tuples of length 2
;

#;(r:struct edge-u (e) #:transparent
          #:methods gen:equal+hash [(r:define equal-proc edge-equal-u?)
                                    (r:define hash-proc edge-hash)
                                    (r:define hash2-proc edge-hash)]
          #:methods gen:custom-write
          [(define write-proc
             (λ (the-e port mode)
               (fprintf port "(~a -- ~a)"
                        (car (edge-u-e the-e))
                        (cdr (edge-u-e the-e)))))])

#;(r:struct edge-d (e) #:transparent)

#;(define (-e- u v)
  (edge-u (r:cons u v)))
(define (-e- u v)
  (set u v))

#;(define (-e-> u v)
  (edge-d (r:cons u v)))
(define (-e-> u v)
  (tpl u v))

; XXX: assuming no symbolic objects are accessed as an edge
; edge-u? rejects symbolic things
(define (edge-u? a-object)
  (if (dp-symbolic? a-object)
      (raise "only concrete sets can be used as edges")
      (and (dp-set? a-object)
           (equal? (length (hash-keys (dp-set-S a-object))) 2))))

; get one of the vertices of an edge
; if the edge is directed, get the starting one
; XXX : this should be safe for verifier
;       assuming no symbolic edge floating around,
;       or symbolic subset of size 2 used as an edge
; TODO : add support for symbolic edge
; 
(define/contract/kc (e-u e)
  (->k ([e (or/kc "expects an edge" edge-u/kc edge-d/kc)])
       any/kc)
  (if (edge-u? e)
      (first (hash-keys (dp-set-S e)))
      (fst e)))

(define (e-u-u e)
  (first (hash-keys (dp-set-S e))))
(define (e-u-d e)
  (fst e))

(provide e-u-typed-rewriter)
(define-syntax e-u-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON (tUEdge)))
       (syntax-parser
         [(e-u e) (cons #'(e-u-u e) (tSymbol))])]
      [(args-τ ('CON (tDEdge)))
       (syntax-parser
         [(e-u e) (cons #'(e-u-d e) (tSymbol))])]
      [(args-τ ('SYM _))
       (λ (stx)
         (raise-syntax-error #f "kv$symbolic not supported yet" stx))]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects an edge, gets ~a"
                                          (map get-τb type-lst)) stx))])))


; get one of the vertices of an edge
; that is different than e-u (unless it is a self-loop)
; if the edge is directed, get the ending one
(define/contract/kc (e-v e)
  (->k ([e (or/kc "expects an edge" edge-u/kc edge-d/kc)])
       any/kc)
  (if (edge-u? e)
      ; use last to taking the self-loop into consideration
      (last (hash-keys (dp-set-S e)))
      (snd e)))

(define (e-v-u e)
  (second (hash-keys (dp-set-S e))))
(define (e-v-d e)
  (snd e))

(provide e-v-typed-rewriter)
(define-syntax e-v-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON (tUEdge)))
       (syntax-parser
         [(e-v e) (cons #'(e-v-u e) (tSymbol))])]
      [(args-τ ('CON (tDEdge)))
       (syntax-parser
         [(e-v e) (cons #'(e-v-d e) (tSymbol))])]
      [(args-τ ('SYM _))
       (λ (stx)
         (raise-syntax-error #f "kv$symbolic not supported yets" stx))]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects an edge, gets ~a"
                                          (map get-τb type-lst)) stx))])))



#;(define (incident? e v)
    (r:or (r:equal? (r:car e) v)
          (r:equal? (r:cdr e) v)))

(provide incident?-typed-rewriter)
; TODO: eliminate the dynamic ``edge-u?'' check completely for verifier
;       by adding other cases
(define-syntax incident?-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ (_ (tUEdge)) ('SYM (tSymbol)))
       (syntax-parser
         [(incident? e v) (cons #'(incident?-u-safe e v) (tBool))])]
      [(args-τ (_ (tUEdge)) ('CON (tSymbol)))
       (syntax-parser
         [(incident? e v) (cons #'(incident? e v) (tBool))])]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects an edge and a vertex, gets ~a"
                                          (map get-τb type-lst)) stx))])))
; if vertex v is one of the endpoints of e
(define/contract/kc (incident? e v)
  (->k ([e (or/kc "expects an edge" edge-u/kc edge-d/kc)]
        [v any/kc])
       any/kc)
  (if (edge-u? e)
        (set-∈ v e)
        (r:or (r:equal? (fst e) v)
              (r:equal? (snd e) v))))

(define (incident?-u-safe e v)
  (set-∈-safe v e))

#;(define (endpoints e)
    (a-set (r:car e) (r:cdr e)))
; get the endpoints of e as a set
(define/contract/kc (endpoints e)
  (->k ([e (or/kc "expects an edge" edge-u/kc edge-d/kc)])
       any/kc)
  (if (edge-u? e)
      e
      (a-set (fst e) (snd e))))
; TODO: add symbolic support, eliminate dynamic ``edge-u?'' check
(provide endpoints-typed-rewriter)
(define-syntax endpoints-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON (tEdge _)))
       (syntax-parser
         [(endpoints e) (cons #'(endpoints e) (tSetOf (tSymbol)))])]
      [(args-τ ('SYM _))
       (λ (stx)
         (raise-syntax-error #f "kv$symbolic not supported yets" stx))]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects an edge, gets ~a"
                                          (map get-τb type-lst)) stx))])))

; how to unify the contract of directed graph and the contract of undirected
; define a function with a parameter specifying directness that returns respectively
#;(define (graph/c #:undirected? [undirected? #f])
    (let ([graph-aux/c
           (hash/c vertex/c (listof vertex/c) #:immutable #t #:flat? #t)])
      (if undirected?
          (and/c
           graph-aux/c
           (λ (g)
             (for/and ([(key values) (in-hash g)])
               (for/and ([v values])
                 (has-edge? key v g)))))
          graph-aux/c)))

; original definition
#;(define graph/c
    (and/c
     (hash/c vertex/c (listof vertex/c) #:immutable #t #:flat? #t)
     ; was undirected
     #;(λ (g)
         (for/and ([(key values) (in-hash g)])
           (for/and ([v values])
             (edge? key v g))))))


; not used in new design
(define empty-graph (make-immutable-hash))
; not used in new design
(define (empty-graph-over-vertices V)
  (for/hash ([v V])
    (values v '())))

; the set of 
(define/contract/kc (get-vertices g)
  (->k ([g dp-graph/kc]) any/kc)
  (dp-graph-V g))

; (hash-ref (dp-graph-M g) u) can be a hash with symbolic values
; which got directly copied to core of the set
(define/contract/kc (neighbors g u)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (dp-set (hash-ref (dp-graph-M g) u)))
(provide neighbors-typed-rewriter)
(define-syntax neighbors-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ (_ (tGraph _)) ('CON (tSymbol)))
       (syntax-parser
         [(neighbors g u) (cons #'(neighbors g u) (tSetOf (tSymbol)))])]
      [(args-τ (_ (tGraph _)) ('SYM _))
       (λ (stx)
         (raise-syntax-error #f "kv$symbolic not supported yets" stx))]
      [_ (λ (stx)
           (raise-syntax-error #f
                               (format "expects a graph and a vertex, gets ~a"
                                       (map get-τb type-lst)) stx))])))

(define/contract/kc (in-neighbors g v)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (dp-set-filter
   (r:λ (u)
        (hash-ref
         (hash-ref (dp-graph-M g) u) v #f))
   (dp-graph-V g)))
(provide in-neighbors-typed-rewriter)
(define-syntax in-neighbors-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ (_ (tGraph _)) ('CON (tSymbol)))
       (syntax-parser
         [(in-neighbors g u) (cons #'(in-neighbors g u) (tSetOf (tSymbol)))])]
      [(args-τ (_ (tGraph _)) ('SYM _))
       (λ (stx)
         (raise-syntax-error #f "kv$symbolic not supported yets" stx))]
      [_ (λ (stx)
           (raise-syntax-error #f (format "expects a graph and a vertex, gets ~a"
                                          (map get-τb type-lst)) stx))])))

(provide out-neighbors-typed-rewriter)
(define-syntax out-neighbors-typed-rewriter
  (syntax-local-value #'neighbors-typed-rewriter))
(define/contract/kc (out-neighbors g u)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (neighbors g u))


(define/contract/kc (degree g u)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (set-size (neighbors g u)))
(define/contract/kc (in-degree g u)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (set-size (in-neighbors g u)))
(define/contract/kc (out-degree g u)
  (->k ([g dp-graph/kc]
        [u (g) (make-simple-contract/kc (v)
                 (set-∈ v (get-vertices g))
                 "expects an vertex of the given graph")])
       any/kc)
  (set-size (neighbors g u)))
;; get edge as pair from graph/c
;; assume directed
#;(define (get-edges g)
    (r:map
     (r:hash-keys g)))

; old version, may not be solvable(?)
#;(define (get-edges g)
    (for*/fold ([edges (hash)]
                #:result (dp-set edges))
               ([l (in-list (hash->list g))]
                [t (in-list (if (list? (cdr l))
                                (cdr l)
                                (list (cdr l))))])
      (cond
        [(hash-ref edges (cons t (car l)) #f)
         (values edges)]
        [else (values (hash-set edges (cons (car l) t) #t))])))


(define/contract/kc (get-edges g)
  (->k ([g dp-graph/kc]) any/kc)
  (r:let
   ([edge-maker
     (r:if (dp-graph-directed? g)
           tpl
           a-set)])
   (dp-set
    (make-immutable-hash
     (r:apply r:append
              (r:map
               (r:λ (u)
                    (r:map
                     (r:λ (v)
                          (r:cons
                           (edge-maker u v)
                           (hash-ref (hash-ref (dp-graph-M g) u) v #f)))
                     (hash-keys (hash-ref (dp-graph-M g) u))))
               (hash-keys (dp-graph-M g))))))))

(define (dp-graph-V-size=-d/kc n)
  (make-simple-contract/kc (g)
      (equal? (dp-int-unwrap (set-size (get-vertices g)))
              (dp-int-unwrap n))               
      (format "expects a graph with ~e vertices" (dp-int-unwrap n))))

(define (dp-graph-E-size=-d/kc n)
  (make-simple-contract/kc (g)
      (equal? (dp-int-unwrap (set-size (get-edges g)))
              (dp-int-unwrap n))               
      (format "expects a graph with ~e edges" (dp-int-unwrap n))))

; XXX: how to keep the invariant that undirected edge can not
;      be inserted to directed graph or vice-versa
;      does not ensure the invariant that the endpoints in E are subset of V
;      no error info when some e with endpoints not in V are inserted
;      need a contract to check this
; unsolvable
; V : (dp-set/c any/c) set of vertices
; E : (dp-set/c edge/c)
#;(define (create-graph V E #:directed? [directed? #f])
  ; XXX: turn this defensive programming into contract
  (when (not
         (andmap
          (λ (e)
            (set-subset-of? (endpoints e) V))
          (dp-set-members->list E)))
    (error "create-graph: some edge contain an endpoint that does not belong to the set of vertices"))
  
  (dp-graph
   (let loop
     ([M (for/hash ([u (dp-set-members->list V)])
           (values u (make-immutable-hash)))]
      [Es (dp-set-members->list E)])
     (if (empty? Es)
         M
         (let* ([u (e-u (car Es))]
                [v (e-v (car Es))])
           (loop (hash-set
                  (if directed?
                      M
                      (hash-set M v (hash-set (hash-ref M v) u #t)))
                  u (hash-set (hash-ref M u) v #t)) (cdr Es)))))
   V
   directed?))

(define-syntax (create-graph stx)
  (syntax-parse stx
    [(_ V E (~optional (~seq #:directed? directed?) #:defaults ([directed? #'#f])))
     #`(dp-graph
        (let loop
          ([M (for/hash ([u (dp-set-members->list
                             (contracted-v/kc
                              dp-set/kc
                              V #,(syntax-srcloc #'V)
                              'create-graph
                              (list "the given vertex set")))])
                (values u (make-immutable-hash)))]
           [Es (dp-set-members->list
                 (contracted-v/kc
                  (and/kc                  
                   (if directed?
                       (dp-setof/kc edge-d/kc)
                       (dp-setof/kc edge-u/kc))
                   (kc-contract (an-E the-srcloc name context [predicate? #f])
                       (let* ([not-in-e
                              (findf
                               (λ (e)
                                 (not (set-subset-of? (endpoints e) V)))
                               (dp-set-members->list an-E))]
                             [not-in-v
                              (if not-in-e
                                  (car (dp-set-members->list
                                        (set-minus (endpoints not-in-e) V)))
                                  #f)])
                           (if not-in-e
                               (contract-fail/kc
                                the-srcloc
                                name
                                (format "endpoint ~v of the edge ~v is not in the set of vertices"
                                        not-in-v not-in-e)
                                context
                                an-E
                                predicate?)
                               an-E))))
                  E #,(syntax-srcloc #'E)
                  'create-graph
                  (list "the given edge set")))])
          (if (empty? Es)
              M
              (let* ([u (e-u (car Es))]
                     [v (e-v (car Es))])
                (loop (hash-set
                       (if directed?
                           M
                           (hash-set M v (hash-set (hash-ref M v) u #t)))
                       u (hash-set (hash-ref M u) v #t)) (cdr Es)))))
        V
        directed?)]))

; create a graph based on a set of edges, with vertices being all
; those appeared as endpoints in these edges
; unsolvable
; E : (dp-set/c edge/c)
#;(define (create-graph-from-edges E #:directed? [directed? #f])
  (create-graph (dp-list->set
                 (apply append
                        (map
                         (λ (e)
                           (dp-set-members->list (endpoints e)))
                         (dp-set-members->list E)))) E #:directed? directed?))
(define-syntax (create-graph-from-edges stx)
  (syntax-parse stx
    [(_ E (~optional (~seq #:directed? directed?) #:defaults ([directed? #'#f])))
     #`(create-graph (dp-list->set
         (apply append
                (map
                 (λ (e)
                   (dp-set-members->list (endpoints e)))
                 (dp-set-members->list
                  (contracted-v/kc
                   (if directed?
                       (dp-setof/kc edge-d/kc)
                       (dp-setof/kc edge-u/kc))
                   E #,(syntax-srcloc #'E)
                   'create-graph-from-edges
                  (list "the argument for edge set")))))) E #:directed? directed?)]))

; remove the orientiation of all edges and make the graph undirected
; nothing should change if input is already undirected
; internal, used for optimization reasons.
; Not lifted with Rosette construct. Even if lifted it
; may cause problem if g is not concrete (contains symbolic value)
; because the existence of certian key in resulting adjacency matrix 
; would depend on the solution of the symbolic value
(define (dp-underlying-u-graph g)
  (let ([adj-M (dp-graph-M g)])
    (dp-graph
     (make-immutable-hash
      (map
       (λ (u)
         (cons
          u
          (for/hash ([v (dp-graph-V-ground g)]
                     #:when (or
                             (hash-ref (hash-ref adj-M u) v #f)
                             (hash-ref (hash-ref adj-M v) u #f)))
            (values
             v
             (if (hash-ref (hash-ref adj-M u) v #f)
                 (hash-ref (hash-ref adj-M u) v)
                 (hash-ref (hash-ref adj-M v) u))))))
       (dp-graph-V-ground g)))
     (dp-graph-V g)
     #f)))

; likely nonsolvable
(define (dp-symbolic-subgraph-core g struct-constr) 
  (values
   (dp-graph
    (if (dp-graph-directed? g)
        (for/hash ([u (dp-set-members->list (dp-graph-V g))])
          (values u
                  (for/hash ([v (hash-keys (hash-ref (dp-graph-M g) u))]
                             #:when (hash-ref (hash-ref (dp-graph-M g) u) v #f))
                    (values v (fresh-symbolic-bool)))))
        (let ([vs (dp-set-members->list (dp-graph-V g))])
          (for*/fold ([adj-M (make-immutable-hash)])
                     ([i (range (length vs))]
                      [j (range i (length vs))]
                      #:when (hash-ref
                              (hash-ref (dp-graph-M g) (list-ref vs i))
                              (list-ref vs j)
                              #f))
            (let* ([x (fresh-symbolic-bool)]
                   [u (list-ref vs i)]
                   [v (list-ref vs j)]
                   [u-adj (hash-ref adj-M u (make-immutable-hash))]
                   [v-adj (hash-ref adj-M v (make-immutable-hash))])
              (hash-set (hash-set adj-M u (hash-set u-adj v x))
                        v (hash-set v-adj u x))))))
      (let-values
          ([(sym-set cstr-lst) (dp-symbolic-subset (dp-graph-V g))])
        sym-set)
      (dp-graph-directed? g))
   struct-constr))

(define (dp-symbolic-subgraph g)
  (dp-symbolic-subgraph-core g (list dp-graph-V-M?)))


; shrinks, nonsolvable
(define (dp-graph-from-sol the-sym-graph a-sol)
  (let ([V-sol (dp-set-from-sol (dp-graph-V the-sym-graph) a-sol)])
    (dp-graph
     (if (r:unsat? a-sol) #f
         (for/hash ([u (dp-ground-set->list V-sol)]
                    #:when (set-∈ u V-sol))
           (values u
                   (for/hash ([v (hash-keys (hash-ref (dp-graph-M the-sym-graph) u))])
                     (values v (hash-ref (r:model a-sol)
                                         (hash-ref
                                          (hash-ref (dp-graph-M the-sym-graph) u)
                                          v)
                                         #f))))))
     V-sol
     (dp-graph-directed? the-sym-graph))))

;
; ★ connectivity ★
; Note: compiles to diffrent implementation in solver and non-solver environment
; for directed graph, it would refers to weakly connectivity
(define-syntax (connected? stx)
  (if (syntax-parameter-value #'dp-solver-env?)
      (syntax-parse stx
        [(_ sym-g (~optional starting-vs))
         #`(dp-r-connected
            (if (dp-graph-directed? sym-g)
                (dp-underlying-u-graph sym-g)
                sym-g)
            #,(if (attribute starting-vs)
                 #'(dp-ground-set->list starting-vs)
                 #'(dp-graph-V-ground sym-g)))])
      (syntax-parse stx
        [(_ g (~optional starting-vs))
         #'(match-let-values
            ([(conn? _ _ _ _) (dp-dfs-pre g #t)])
            conn?)])))
(kv-func-type-annotate connected? ((tGraph _) (tBool)) "a graph")

; constraint added to the solver that enforces every vertex selected
; has an incoming path from lower ordered node
; sym-g-V-hash -- the symbolic set of vertices of a (symbolic) graph
; sym-g-M-hash -- the symbolic adjacent matrix of a (symbolic) graph
; sym-v-order -- the symbolic ordering of the (selected) vertices
;                can be created on the go
; Note: theoretically this construct also works as a predicate for
; concrete values, where sym-v-order is the dfs pre-ordering for g.
; But it is not intended to be used in the way, as getting connectivity
; or reachability can already be checked when obtaining the dfs pre-ordering
; with regular dfs
(define (dp-r-path-constraint sym-g-V-hash sym-g-M-hash sym-v-order)
  (r:andmap
   (r:λ (v)
        (r:implies
         ; if v is selected
         (hash-ref sym-g-V-hash v) 
         (r:and
          ; all ordering index (like dfs-pres) is nonnegative
          (r:>= (hash-ref sym-v-order v) 0)
          ; either it is the first vertex
          (r:or (r:= (hash-ref sym-v-order v) 0)
                (r:ormap
                 (r:λ (u)
                      (r:and
                       ; begin -- original version (assume g undirected)
                       ; if there's one u connecting to v (assume g undirected)
                       ;(hash-ref (hash-ref sym-g-M-hash v) u #f)
                       ; end -- original version
                       (hash-ref (hash-ref sym-g-M-hash u) v #f) ; goes first, maybe can filtering out concrete #f
                       (hash-ref sym-g-V-hash u)                  
                       ; u is reached earlier than v, i.e., has a lower index
                       (r:< (hash-ref sym-v-order u) (hash-ref sym-v-order v))))
                       ; alternatively -- u is the parent of v in the search tree, i.e. 
                       ; not sure if more efficient (seems not with steiner tree)
                       ;(r:= (hash-ref sym-v-order u) (r:- (hash-ref sym-v-order v) 1))))
                       ; end -- alternative
                 ; from all the vertices that v connects to
                 ; begin -- old version (assume g undirected)
                 ;(hash-keys (hash-ref sym-g-M-hash v))
                 ; end -- old version
                 ; Note: there is an overhead here trying all potential vertices
                 ; we can potentially optimize this by providing an inward adjacency matrix
                 (hash-keys sym-g-V-hash)
                 )))))
   (hash-keys sym-g-V-hash)))

;
; sym-g : symbolic graph produced by dp-symbolic-subgraph
; possible-start-vs : (listof vertex/c)
; assume possible-start-vs are valid vertices of sym-g
; assume sym-g undirected
(define (dp-r-connected sym-g possible-start-vs)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)]
    [v-order
     (make-immutable-hash
      (r:map
       (r:λ (v)
            (r:cons v
                    (fresh-symbolic-int)))
       (hash-keys g-V-hash)))])
   (r:and
    ; exact 1 of the vertices selected is starting vertex with order index 0
    (r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      possible-start-vs)
     1)
    ; exact 1 of the vertices selected is starting vertex with order index 0 (among all vertices)
    (r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      (hash-keys g-V-hash))
     1)
    ; vertex outside possible-start-vs can not have index 0
    #;(r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (hash-ref possible-start-vs v #f)))
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )))

#;(define (dp-r-test sym-g possible-start-vs v-order)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)])
   (r:and
    ; exact 1 of the vertices selected is starting vertex with order index 0
    (r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      possible-start-vs)
     1)
    #;(r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      (hash-keys g-V-hash))
     1)
    (r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (r:member v possible-start-vs)))
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )))

; FIXME: remove this later
(define (dp-r-st-test sym-g s t v-order)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)])
   (r:and
    ; s must be selected in the subgraph
    (hash-ref g-V-hash s)
    ; t must be selected in the subgraph
    (hash-ref g-V-hash t)
    ; 
    (r:= (hash-ref v-order s) 0)
    ; no other selected vertices can be used as the starting point
    (r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (equal? v s))) ; intentionally fallback to racket
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )
   ))

(define (dp-r-st-reachable sym-g s t)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)]
    ; there exists some ordering of the vertices
    [v-order
     (make-immutable-hash
      (r:map
       (r:λ (v)
            (r:cons v
                    (fresh-symbolic-int)))
       (hash-keys g-V-hash)))])
   (r:and
    ; s must be selected in the subgraph
    (hash-ref g-V-hash s)
    ; t must be selected in the subgraph
    (hash-ref g-V-hash t)
    ; s has index 0 in the order
    (r:= (hash-ref v-order s) 0)
    ; no other selected vertices can be used as the starting point
    (r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (equal? v s))) ; intentionally fallback to racket
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )))

(define-syntax (reachable? stx)
  (if (syntax-parameter-value #'dp-solver-env?)
      (syntax-parse stx
        [(_ sym-g s t)
         #'(dp-r-st-reachable sym-g s t)])
      (syntax-parse stx
        [(_ g s t)
         #'(match-let-values
            ([(pres _ _ _)
              (dp-do-dfs g #f (list s) (hash) (hash) (hash s 0) #t 0)])
            (hash-ref pres t #f))])))
(kv-func-type-annotate reachable? ((tGraph _) (tSymbol) (tSymbol) (tBool))
                       "a graph and two vertices")

;
(define (dp-r-test sym-g v-order)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)]
    [directed? (dp-graph-directed? sym-g)])
   (r:andmap
    (r:λ (u)
         (r:implies
          (hash-ref g-V-hash u #f)
          (r:if directed?
                (r:andmap
                 (r:λ (v)
                      (r:implies
                       ; if the edge from u to v is selected (v is known to be selected if so)
                       (hash-ref (hash-ref g-M-hash u) v #f)
                       ; the index order of u must be smaller than that of v
                       (r:< (hash-ref v-order u) (hash-ref v-order v))
                       ))
                 (hash-keys (hash-ref g-M-hash u)))
                (r:<=
                 (r:count
                  r:identity
                  (r:map
                   (r:λ (v)
                        ; at most 1 this is violated
                        (r:not
                         (r:implies
                          ; if the edge from u to v is selected (v is known to be selected if so)
                          (hash-ref (hash-ref g-M-hash u) v #f)
                          ; the index order of u must be smaller than that of v
                          (r:< (hash-ref v-order u) (hash-ref v-order v))
                          )))
                   (hash-keys (hash-ref g-M-hash u))))
                 1))))
    (hash-keys g-V-hash))))

; TODO: unsure how efficient
(define (dp-r-acyclic sym-g)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)]
    [v-order
     (make-immutable-hash
      (r:map
       (r:λ (v)
            (r:cons v
                    (fresh-symbolic-int)))
       (hash-keys g-V-hash)))]
    [directed? (dp-graph-directed? sym-g)])
   (r:andmap
    (r:λ (u)
         (r:implies
          (hash-ref g-V-hash u #f)
          (r:if directed?
                (r:andmap
                 (r:λ (v)
                      (r:implies
                       ; if the edge from u to v is selected (v is known to be selected if so)
                       (hash-ref (hash-ref g-M-hash u) v #f)
                       ; the index order of u must be smaller than that of v
                       (r:< (hash-ref v-order u) (hash-ref v-order v))
                       ))
                 (hash-keys (hash-ref g-M-hash u)))
                (r:<=
                 (r:count
                  r:identity
                  (r:map
                   (r:λ (v)
                        (r:not
                         (r:implies
                          ; if the edge from u to v is selected (v is known to be selected if so)
                          (hash-ref (hash-ref g-M-hash u) v #f)
                          ; the index order of u must be smaller than that of v
                          (r:< (hash-ref v-order u) (hash-ref v-order v))
                          )))
                   (hash-keys (hash-ref g-M-hash u))))
                 1))))
    (hash-keys g-V-hash))))

(define-syntax (acyclic? stx)
  (if (syntax-parameter-value #'dp-solver-env?)
      (syntax-parse stx
        [(_ sym-g)
         #'(dp-r-acyclic sym-g)])
      (syntax-parse stx
        [(_ g)
         #'(match-let-values
            ([(_ ac? _ _ _) (dp-dfs-pre g #f)])
            ac?)])))
(kv-func-type-annotate acyclic? ((tGraph _) (tBool)) "a graph")

; check if g is a s-t path
; TODO: potentially optimize this by having
; a modified dp-r-path-constraint asking exact-1-of at ormap
; Note: use syntax instead of function because (reachable? g s t) needs to
; expand differently in verifier and solver environment
(define-syntax (st-path? stx)
  (syntax-parse stx
    [(_ g s t)
     #`(let ([g-V-hash (dp-set-S (dp-graph-V g))])
         (r:and
          (reachable? g s t)
          (r:andmap
           (r:λ (v)
                (r:implies
                 (hash-ref g-V-hash v)
                 (r:and (r:<= (in-degree g v)
                              (if (dp-graph-directed? g) 1 2))
                        (r:<= (out-degree g v)
                              (if (dp-graph-directed? g) 1 2))))
                ;(r:<= (set-size (set-∪ (out-neighbors g v) (in-neighbors g v))) 2)
                )
           (hash-keys g-V-hash))
          (r:= (in-degree g s) (if (dp-graph-directed? g) 0 1))
          (r:= (out-degree g s) 1)  
          ;(r:= (set-size (set-∪ (out-neighbors g s) (in-neighbors g s))) 1)
          (r:= (in-degree g t) 1)
          (r:= (out-degree g t) (if (dp-graph-directed? g) 0 1))
          ;(r:= (set-size (set-∪ (out-neighbors g t) (in-neighbors g t))) 1)
          ))]))
(kv-func-type-annotate st-path? ((tGraph _) (tSymbol) (tSymbol) (tBool)) "a graph")
#;(define (st-path? g s t)
  (let ([g-V-hash (dp-set-S (dp-graph-V g))])
    (r:and
     ; XXX: this does not work in both verifier and solver environment
     ;(reachable? g s t)
     (dp-r-st-reachable g s t)
     (r:andmap
      (r:λ (v)
           (r:implies
            (hash-ref g-V-hash v)
            (r:and (r:<= (in-degree g v)
                         (if (dp-graph-directed? g) 1 2))
                   (r:<= (out-degree g v)
                         (if (dp-graph-directed? g) 1 2))))
           ;(r:<= (set-size (set-∪ (out-neighbors g v) (in-neighbors g v))) 2)
           )
      (hash-keys g-V-hash))
     (r:= (in-degree g s) (if (dp-graph-directed? g) 0 1))
     (r:= (out-degree g s) 1)  
     ;(r:= (set-size (set-∪ (out-neighbors g s) (in-neighbors g s))) 1)
     (r:= (in-degree g t) 1)
     (r:= (out-degree g t) (if (dp-graph-directed? g) 0 1))
     ;(r:= (set-size (set-∪ (out-neighbors g t) (in-neighbors g t))) 1)
     )))

(define (dp-symbolic-path g s t)
  (dp-symbolic-subgraph-core g
                             (list dp-graph-V-M?
                                   (r:λ (g) (st-path? g s t)))))

; a single component dfs
; g : graph/c
; weak : boolean? -- the underlying undirected graph of g will be used (no effect when g is already undirected)
; stack : (listof vertex/c) -- vertices to visit at this point of the recursion
; pres : (hash/c vertex/c natural?) -- pre-ordering index
; parents : (hash/c vertex/c vertex/c) -- parent of the vertices visiting so far in the tree
; components : (hash/c vertex/c natural?) -- connected component index
; ac? : boolean? -- if the graph is connected
; t : current timestamp
; -> (values/c (hash/c vertex/c natural?) (hash/c vertex/c vertex/c) (hash/c vertex/c natural?) boolean?)
(define (dp-do-dfs g weak? stack pres parents components ac? t) ; add an argument directed?
    (if (empty? stack)
        ; no node to visit any more, return
        ; #t for acyclic
        (values pres parents components ac?)
        ; now is visiting v
        (let* ([v (car stack)]
               [component-v (hash-ref components v)]
               [neighbor-set (if weak?
                                 (set-∪ (in-neighbors g v) (neighbors g v))
                                 (neighbors g v))]
               [ns (dp-set-members->list
                    (dp-set-remove
                     neighbor-set
                     (hash-ref parents v #f)))]
               [ns-same-component
                (filter
                 (λ (u)
                   (or
                    ; has not visisted yet
                    (not (hash-ref components u #f))
                    ; visited and also in the same component
                    (equal? (hash-ref components u) component-v)))
                 ns)]
               [to-visit
                (filter
                 (λ (u)
                   (not (hash-ref pres u #f)))
                 ns-same-component)]
               [ac-this? (equal? (length to-visit) (length ns-same-component))])
          (dp-do-dfs g
                     weak?
                     (append to-visit (cdr stack))
                     (hash-set pres v t)
                     (foldl (λ (u p-accu) (hash-set p-accu u v)) parents to-visit)
                     (foldl (λ (u p-accu) (hash-set p-accu u component-v)) components to-visit)
                     (and ac? ac-this?)
                     (+ 1 t)))))

; -> boolean? boolean? (values/c (hash/c vertex/c integer?) (hash/c vertex/c vertex/c) )
;  :  connected?, acyclic?, pre-ordering, parent and component
; weak? -- traverse the underlying undirected graph instead (see dp-do-dfs)
; internal
(define (dp-dfs-pre g weak?)

  (define (visit-all-component g weak? vs conn? ac? pres parents components)
    (if (empty? vs)
        (values conn? ac? pres parents components)
        (let ([v (car vs)]
              [t-now (apply max (cons -1 (hash-values pres)))])
          (if (hash-ref pres v #f)
              ; ignore this node as already visited
              (visit-all-component g weak? (cdr vs) conn? ac? pres parents components)
              ; visit this component
              (let-values
                  ([(pres-now parents-now components-now ac?-now)
                    (dp-do-dfs g weak? (list v) pres parents (hash-set components v (+ t-now 1)) ac? (+ t-now 1))])
                (visit-all-component
                 g
                 weak?
                 (cdr vs)
                 (if
                  ; pres is empty
                  (equal? t-now -1)
                  conn?
                  ; otherwise, g has more than one component
                  #f)
                 ac?-now
                 pres-now
                 parents-now
                 components-now)
                )))))
    

  (begin
    (visit-all-component
   g
   weak?
   (dp-set-members->list (dp-graph-V g))
   #t
   #t
   (hash)
   (hash)
   (hash))))

; old version
; graph traversal
; get pre-order, search-tree and list of vertices ordered by pre-order
; g: graph/c
; -> (values (hash/c vertex/c integer?) graph-e/c (listof vertex/c))
(define (dfs-pre g)
  ; parent is also a stack
  (define (dfs g stack parent order v-order tree)
    (if (empty? stack) (values v-order tree)
        ;else
        (let ([v (car stack)]
              [s-tail (cdr stack)])
          (cond
            ; if v alreay visited
            [(hash-ref v-order v #f)
             (dfs g s-tail (cdr parent) order v-order tree)]
            ; visit v
            [else
             (dfs g
                  ; add all neighbors of v to the stack
                  (append (hash-ref g v) s-tail)
                  (append (map (λ (u) v) (hash-ref g v)) (cdr parent))
                  (+ 1 order)
                  ; mark v as visited with timestamp
                  (hash-set v-order v order)
                  ; add the edge from v's parent to v
                  (if (car parent)
                      (hash-set tree (cons (car parent) v) #t)
                      tree
                      ))]))))
  ; visit multiple connecting components
  (define (dfs-pre-aux g vs v-order tree)
    (cond [(empty? vs) (values v-order tree)]
          ; (visited? (car vs))
          [(hash-ref v-order (car vs) #f)
           (dfs-pre-aux g (cdr vs) v-order tree)]
          [else
           (let-values
               ([(v-order-next tree-next)
                 (dfs g
                      (list (car vs))
                      '(#f)
                      (+ (apply
                          max
                          ; make first node -1 + 1 = 0
                          (cons -1 (hash-values v-order)))
                         1)
                      v-order
                      tree)])
             (dfs-pre-aux
              g
              (cdr vs)
              v-order-next
              tree-next
              ))]))
  
  (define-values (v-order tree)
    (dfs-pre-aux g (hash-keys g) (hash) empty-graph))
  
  (define vs (sort (hash-keys v-order)
                   (λ (x y)
                     (< (hash-ref v-order x)
                        (hash-ref v-order y)))))

  (values v-order tree vs))

#;(module+ test
  (require rackunit
           racket/pretty)
  (test-case
   "DFS test"
   (let* ([a-g (make-hash '((v1 v2 v3 v4 v5)
                            (v2 v1 v4 v6)
                            (v3 v1 v5)
                            (v4 v1 v2 v5 v6)
                            (v5 v1 v3 v4 v6)
                            (v6 v2 v4 v5)
                            (v7 v8 v9)
                            (v8 v7)
                            (v9 v7)))])
     (let-values
         ([(v-order order vs) (dp-dfs-pre a-g)])
       (pretty-print v-order)
       (pretty-print order)
       (pretty-print vs)))
   ))

; create list of vertices
(define (vi i)
  (string->symbol
   (string-append "v"
                  (number->string i))))

; random graph generation
(define (generate-random-graph-sample-edge n m
                                           #:directed? [directed? #f]
                                           #:no-isolated-vertex? [no-iso? #f])
  (define vs
    (map vi (range 1 (+ 1 n))))

  (define es
    (map
     ; cartesian-product gives list of list instead of list of pairs
     (λ (lst)
       (let ([edge-maker
              (if directed?
                  tpl
                  a-set)])
         (edge-maker (first lst) (second lst))))
     (random-sample
      (remove-duplicates
       (filter
        (λ (lst) (not (equal? (first lst) (second lst))))
        (cartesian-product vs vs))
       (if directed?
           equal?
           (λ (l1 l2)
             (and
              (equal? (first l1) (second l2))
              (equal? (second l1) (first l2))))))
      m #:replacement? #f)))

  (define E (dp-list->set es))
  (define V
    (if no-iso?
        (dp-list->set
         (filter
          (λ (v)
            (ormap
             (λ (e) 
               (set-∈ v (endpoints e)))
             es))
          vs))
        (dp-list->set vs)))

  (create-graph V E #:directed? directed?))


; parsing

(define-syntax (graph stx)
  (if (dp-parse-table)
      (if
       (not (dp-part-cert-env?))
       (syntax-parse stx
         [(_ (~optional (~or (~and #:directed pv-directed?) #:undirected))
             (~optional (~seq #:v-size pv-v-size))
             (~optional (~seq #:e-size pv-e-size)))
          (let* ([directed (if (attribute pv-directed?) #t #f)]
                 [maybe-v-size (if (attribute pv-v-size) #'pv-v-size #f)]
                 [maybe-e-size (if (attribute pv-e-size) #'pv-e-size #f)]
                 [v-size-as-num (get-size-as-num maybe-v-size)]
                 [e-size-as-num (get-size-as-num maybe-e-size)])
            (dp-stx-type-desc
             (generate-temporary #'graph)
             type 'graph
             kv-type-object (if directed
                                #'(tDGraph)
                                #'(tUGraph))
             atomic? #f
             ctc #`(and/kc
                    #,(if directed
                          #'dp-graph-d/kc
                          #'dp-graph-u/kc)
                    #,(if v-size-as-num
                          #`(dp-graph-V-size=-d/kc #,v-size-as-num)
                          #'any/kc)
                    #,(if e-size-as-num
                          #`(dp-graph-E-size=-d/kc #,e-size-as-num)
                          #'any/kc))
             #;(and/c
                    (λ (a-graph)
                      (and
                       #,(if v-size-as-num
                          #`(equal? (set-size (get-vertices a-graph)) #,v-size-as-num)
                          #'#t)
                       #,(if e-size-as-num
                          #`(equal? (set-size (get-edges a-graph)) #,e-size-as-num)
                          #'#t)))
                    #,(if directed
                          #'dp-graph-d/c
                          #'dp-graph-u/c))
             v-dep-ctc #`(λ (a-inst)
                           (and/kc
                            #,(if (and maybe-v-size (not v-size-as-num))
                                  #`(dp-graph-V-size=-d/kc
                                     #,(instance-field-ref #'a-inst maybe-v-size))
                                  #'any/kc)
                            #,(if (and maybe-e-size (not e-size-as-num))
                                  #`(dp-graph-E-size=-d/kc
                                     #,(instance-field-ref #'a-inst maybe-e-size))
                                  #'any/kc)))
             type-data (list (cons 'directed directed)
                             (cons 'v-size maybe-v-size)
                             (cons 'e-size maybe-e-size))
             accessors (list (cons 'vertices #'get-vertices)
                             (cons 'edges #'get-edges)
                             (cons 'graph #'identity))
             generator #`(λ (a-inst)
                           (λ ()
                             (generate-random-graph-sample-edge 8 15 #:directed? #,directed)))
             referred-ids (append
                           (if (and maybe-v-size (not v-size-as-num)) #'maybe-v-size '())
                           (if (and maybe-e-size (not e-size-as-num)) #'maybe-e-size '()))))]
         [_:id #'(graph)])
       (raise-syntax-error #f unsupport-in-certificate-msg stx))
      ; XXX: temporary solution
      (syntax-parse stx
        [(_ lst (~optional (~and #:directed directed)))
         #:with directed? (if (attribute directed) #'#t #'#f)
         #'(let ([M (make-immutable-hash
                     (map
                      (λ (l)
                        (cons (car l)
                              (for/hash ([v (cdr l)])
                                (values v #t))))
                      lst))])
             (dp-graph M (dp-list->set (hash-keys M)) directed?))])))

(define-syntax (vertices-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ graph-like-name:id)
         (let*
             ([the-graph-like (get-field-from-parsed #'graph-like-name)]
              [the-graph-like-vertices-accessor (dp-stx-type-info-accessor-ref the-graph-like 'vertices)]
              [v-size
               (if (equal? the-graph-like-vertices-accessor 'undefined)               
                   (raise-syntax-error
                    #f
                    "object has no vertices"
                    stx
                    #'graph-like-name)
                   (dp-stx-type-info-data-ref the-graph-like 'v-size))]
              [upstream-accessor the-graph-like-vertices-accessor]
              [upstream-ids (cons
                             #'graph-like-name
                             (dp-stx-type-info-field the-graph-like referred-ids '()))])
           (dp-stx-type-info
            (generate-temporary #'vertices-of)
            type 'set
            kv-type-object #'(tSetOf (tSymbol))
            atomic? #f
            ctc #'(dp-setof/kc any/kc)
            v-dep-ctc #`(dp-setof-d/kc v-dep-any/kc)
            upstream #'graph-like-name
            upstream-accessor upstream-accessor
            type-data (list (cons 'el-type
                                  (dp-stx-info
                                   type 'element
                                   kv-type-object #'(tSymbol)
                                   atomic? #f ; you don't know what's inside, vertices may be sets
                                   ctc #'any/kc
                                   v-dep-ctc #'v-dep-any/kc
                                   type-data '()
                                   accessors '()))
                            (cons 'v-size v-size))
            accessors (list (cons 'set #'identity))
            referred-ids upstream-ids))])
      ; XXX: this may not work for other types of graph-like
      (syntax-parse stx
        [(_ g) #'(get-vertices g)]))
  )
(kv-func-type-annotate vertices-of ((tGraph _) (tSetOf (tSymbol))) "a graph")

(define-syntax (edges-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ graph-like-name:id)
         (let*
             ([the-graph-like (get-field-from-parsed #'graph-like-name)]
              [the-graph-like-edges-accessor (dp-stx-type-info-accessor-ref the-graph-like 'edges)]
              [e-size
               (if (equal? the-graph-like-edges-accessor 'undefined)               
                   (raise-syntax-error
                    #f
                    "object has no edges"
                    stx
                    #'graph-like-name)
                   (dp-stx-type-info-data-ref the-graph-like 'e-size))]
              [upstream-accessor the-graph-like-edges-accessor]
              [upstream-ids (cons
                             #'graph-like-name
                             (dp-stx-type-info-field the-graph-like referred-ids '()))])
           (dp-stx-type-info
            (generate-temporary #'edges-of)
            type 'set
            kv-type-object (if (dp-stx-type-info-data-ref the-graph-like 'directed)
                               #'(tSetOf (tDEdge))
                               #'(tSetOf (tUEdge)))
            atomic? #f
            ctc #'(dp-setof/kc any/kc)
            v-dep-ctc #`(dp-setof-d/kc v-dep-any/kc)
            upstream #'graph-like-name
            upstream-accessor upstream-accessor
            type-data (list (cons 'el-type
                                  (dp-stx-info
                                   type 'element
                                   kv-type-object (if (dp-stx-type-info-data-ref
                                                       the-graph-like
                                                       'directed)
                                                      #'(tDEdge)
                                                      #'(tUEdge))
                                   atomic? #f ; you don't know what's inside, edges may be sets
                                   ctc #'any/kc
                                   ; Question: Do we assume the edges set is given so 
                                   ;           it always complies the contract? (why we put any/c here)
                                   v-dep-ctc #'v-dep-any/kc
                                   type-data '()
                                   accessors '()))
                            (cons 'e-size e-size))
            accessors (list (cons 'set #'identity))
            referred-ids upstream-ids))])
      (syntax-parse stx
        [(_ g) #'(get-edges g)])))
(kv-func-type-annotate edges-of ((tGraph dir?) (tSetOf (tEdge dir?))) "a graph")

(define-syntax (subgraph-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ graph-like-name:id)
         (let*
             ([the-graph-like (get-field-from-parsed #'graph-like-name)]
              [directed (dp-stx-type-info-data-ref the-graph-like 'directed)]
              [upstream #'graph-like-name]
              [upstream-accessor (let ([upstream-accessor (dp-stx-type-info-accessor-ref the-graph-like 'graph)])
                                   (if (equal? upstream-accessor 'undefined)
                                       (raise-syntax-error #f "can not be used as a graph" #'graph-like-name )
                                       upstream-accessor))]
              [v-dep-ctc #`(λ (a-inst)
                             (subgraph-of-d/kc
                              (#,upstream-accessor ; which is actually identity if the-graph-like is a graph
                                                   ; upstream-accessor's value is a syntax object #'identity
                               #,(trace-upstream-to-field upstream #'a-inst))))]
              [upstream-ids (cons
                             #'graph-like-name
                             (dp-stx-type-info-field the-graph-like referred-ids '()))])
           (dp-stx-type-desc
            (generate-temporary #'subgraph-of)
            type 'graph
            kv-type-object #`#,(dp-stx-type-info-field the-graph-like kv-type-object)
            atomic? #f
            ctc (if directed
                    #'dp-graph-d/kc
                    #'dp-graph-u/kc)
            v-dep-ctc v-dep-ctc
            type-data (list (cons 'directed directed))
            accessors (list (cons 'vertices #'get-vertices)
                            (cons 'edges #'get-edges)
                            (cons 'graph #'identity))
            generator #`(λ (a-inst)
                          (λ ()
                            (let ([all-edges 
                                   (edges-of
                                    (#,upstream-accessor
                                     #,(trace-upstream-to-field upstream #'a-inst)))])
                              (create-graph-from-edges
                               (random-subset
                                all-edges
                                (random (quotient (set-size all-edges) 2) (set-size all-edges)))))))
            ; procedure to create symbolic certificate from the object
            symbolic-constructor #`(λ (a-inst)
                                     (λ ()
                                       (dp-symbolic-subgraph
                                        (#,upstream-accessor
                                         #,(trace-upstream-to-field upstream #'a-inst)))))
            ; procedure decoding the certificate from solution object of the solver
            solution-decoder #'dp-graph-from-sol
            ; null object for no solution
            null-object #`(dp-graph #f dp-null-set #,directed)
            upstream #'graph-like-name
            upstream-accessor upstream-accessor
            referred-ids upstream-ids))])
      (raise-syntax-error #f "can not be used outside the problem definition" stx)))

(define-syntax (vertex-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ value-with-vertex-name:id)
         (let*
             ([value-with-vertex (get-field-from-parsed #'value-with-vertex-name)]
              [upstream #'value-with-vertex-name]
              [upstream-accessor (let ([upstream-accessor (dp-stx-type-info-accessor-ref value-with-vertex 'vertices)])
                                   (if (equal? upstream-accessor 'undefined)
                                       (raise-syntax-error #f "object has no vertices" #'value-with-vertex-name)
                                       upstream-accessor))]
              [v-dep-ctc #`(λ (a-inst)
                             (make-simple-contract (a-vertex)
                               (set-∈
                                a-vertex
                                (#,upstream-accessor
                                 #,(trace-upstream-to-field upstream #'a-inst))
                                )
                               (format "expects a vertex of the graph ~e"
                                       (#,upstream-accessor
                                        #,(trace-upstream-to-field upstream #'a-inst)))))]
              [upstream-ids (cons
                             #'value-with-vertex-name
                             (dp-stx-type-info-field value-with-vertex referred-ids '()))])
           (dp-stx-type-desc
            (generate-temporary #'vertex-of)
            type 'vertex
            kv-type-object #'(tSymbol)
            atomic? #t
            ctc #'any/kc
            v-dep-ctc v-dep-ctc
            type-data '()
            accessors (list (cons 'vertex #'identity))
            generator #`(λ (a-inst)
                          (λ ()
                            (random-ref
                             (dp-set-members->list
                              (#,upstream-accessor
                               #,(trace-upstream-to-field upstream #'a-inst))))))
            upstream #'value-with-vertex-name
            upstream-accessor upstream-accessor
            referred-ids upstream-ids))])
      (raise-syntax-error #f "can not be used outside the problem definition" stx)))

(define-syntax (path stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ #:in graph-like-name:id #:from s-name:id #:to t-name:id)
         (let*
             ([the-graph-like (get-field-from-parsed #'graph-like-name)]
              [the-source (get-field-from-parsed #'s-name)]
              [the-target (get-field-from-parsed #'t-name)]
              [undirected (dp-stx-type-info-field the-graph-like undirected?)]
              [upstream (list #'graph-like-name #'s-name #'t-name)]
              [upstream-accessor (let ([upstream-graph-accessor (dp-stx-type-info-field the-graph-like graph-accessor)]
                                       [s-v-accessor (dp-stx-type-info-field the-source vertex-accessor)]
                                       [t-v-accessor (dp-stx-type-info-field the-target vertex-accessor)])
                                   (if (equal? upstream-graph-accessor 'undefined)
                                       (raise-syntax-error #f "can not be used as a graph" #'graph-like-name)
                                       (if (equal? s-v-accessor 'undefined)
                                           (raise-syntax-error #f "can not be used as a vertex" #'s-name)
                                           (if (equal? t-v-accessor 'undefined)
                                               (raise-syntax-error #f "can not be used as a vertex" #'t-name)
                                               (if
                                                (free-identifier=? #'s-name #'t-name)
                                                (raise-syntax-error #f "the from and to of a path must be different" stx)
                                                (list upstream-graph-accessor s-v-accessor t-v-accessor))))))]
              [v-dep-ctc #`(λ (a-inst)                           
                             ; XXX: this does not work if g s t are no longer ids
                             (and/kc
                              (subgraph-of-d/kc
                               (#,(list-ref upstream-accessor 0)
                                #,(trace-upstream-to-field (list-ref upstream 0) #'a-inst)))
                              (make-simple-contract (a-graph)
                               (st-path? a-graph
                                        (#,(list-ref upstream-accessor 1)
                                         #,(trace-upstream-to-field (list-ref upstream 1) #'a-inst))
                                        (#,(list-ref upstream-accessor 2)
                                         #,(trace-upstream-to-field (list-ref upstream 2) #'a-inst)))
                               (format
                                "expects a path from ~e to ~e"
                                (#,(list-ref upstream-accessor 1)
                                 #,(trace-upstream-to-field (list-ref upstream 1) #'a-inst))
                                (#,(list-ref upstream-accessor 2)
                                 #,(trace-upstream-to-field (list-ref upstream 2) #'a-inst))))))]
              [upstream-ids (append
                             (list
                              #'graph-like-name
                              #'s-name
                              #'t-name)
                             (dp-stx-type-info-field the-graph-like referred-ids '()))])
           (dp-stx-type-desc
            (generate-temporary #'path-of)
            type 'graph
            atomic? #f
            ctc (if undirected
                    #'dp-graph-u/kc
                    #'dp-graph-d/kc)
            v-dep-ctc v-dep-ctc
            undirected? undirected
            ; (non-symbolic) accessors are on the value of this type
            vertices-accessor #'get-vertices
            edges-accessor #'get-edges
            graph-accessor #'identity
            ; procedure to create symbolic certificate from the object
            symbolic-accessor #'dp-symbolic-path
            ; procedure decoding the certificate from solution object of the solver
            solution-decoder #'dp-graph-from-sol
            ; null object for no solution
            null-object #`(dp-graph #f dp-null-set #,(if undirected #'#f #'#t))
            upstream upstream
            upstream-accessor upstream-accessor
            referred-ids upstream-ids))])
      (raise-syntax-error #f "can not be used outside the problem definition" stx)))
