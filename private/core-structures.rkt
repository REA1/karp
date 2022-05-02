#lang racket

(require
  "verifier-type.rkt"
  "primitive-data-type.rkt"
  "problem-definition-utility.rkt"
  racket/generic
  [for-syntax racket/list
              racket/struct
              racket/syntax
              racket/function
              syntax/parse
              syntax/id-table
              syntax/stx
              racket/match]
  [for-meta 2 racket/base
              syntax/parse]
  [prefix-in r: rosette/safe])

(provide
 ; mergeable interface
 gen:dp-mergeable
 dp-mergeable?
 gen-merge-union
 gen-decode-merged-from-sol
 gen-representative-el-from-lst)


;
; mergable interface
; structure the symbolic union of which can be merged
; see also : element-of
;
(define-generics dp-mergeable
  ; U : the symbolic union to be merged
  ; dp-mergeable : this argument should be a value of a component of the symbolic union
  (gen-merge-union U dp-mergeable)
  (gen-representative-el-from-lst v-lst dp-mergeable) ; the last argument is a dummy used for dispatch
  (gen-decode-merged-from-sol dp-mergeable sol)
  ;#:defaults ([(const #t) (define (gen-merge-union U x) U)])
  )


(provide

 dont-care
 element)

; set structure related
(provide
 (r:struct-out dp-set)
 dp-set/c
 dp-setof/c
 dp-setof-d/c
 a-set
 set-∈
 set-∉
 set-∈-safe
 set-∉-safe
 dp-list->hash
 dp-list->set
 dp-list-list->set
 set-ground-set
 dp-ground-set->list
 dp-set-members->list
 set-subset-of?
 set-equal?

 dp-set-shrink
 
 set
 subset-of
 the-set-of
 the-product-of
 element-of
 
 as-set
 set-∪
 set-∩
 dp-set-remove
 dp-set-filter
 set-minus
 set-size

 dp-null-set
 dp-symbolic-subset
 dp-set-from-sol

 dp-element-from-sol

 ;temp

 dp-symbolic-element-of

 dp-extract-singleton
)



; ---- discarded currently, maybe switch to this design in the future ----
; element
; struct wrapping something, mainly symbol, as id.
; e.g. a number in 2-partition, a vertex of graph, a item in knapsack, etc.
; wrapping a raw symbol enables attaching chaperone properties,
; values, i.e., the value of the number,
;               the weight of the vertex,
;               the value and weight of the item,
; are attached in the chaperone properties
; id : any/c
;

#;(define-values (el-attr has-attr? get-attr)
    (make-impersonator-property 'attr))

#;(r:struct dp-element (id)
          #:methods gen:custom-write
          [(define write-proc
             (r:λ (the-el port mode)
                  (fprintf port "[id:~a, ~a]"
                           (el-id the-el)
                           (let ([the-attr (get-attr the-el)])
                             (string-join
                              (for/list ([(k v) (in-hash the-attr)])
                                (format "~a:~a" k v))
                              ", ")))))])
; ------- end of discarded ------
; ------------------------------------



;
; set operations
;

; check if set-a and set-b has the same elements
; set-a : dp-set/c
; set-b : dp-set/c
; -> boolean?
; NOTE: define here as gen:equal+hash needs to refer to
(define (set-equal? set-a set-b [recursive-equal? #f])
  ; intentional fallback to Racket
  (if (or (not (dp-set-S set-a)) (not (dp-set-S set-b)))
      (and (not (dp-set-S set-a)) (not (dp-set-S set-b)))
      (r:and
       (set-subset-of? set-a set-b)
       (set-subset-of? set-b set-a))))

;
; get the solved set from the rosette solution
; a-sol : r:solution? 
; the-sym-set : (), assumed to be consistent with the solution
; old version, only works on sets every hash value of which is a single (symbolic or concrete) constant
#;(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let ([sym-set-hash (dp-set-S the-sym-set)])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (hash-ref (r:model a-sol)
                                    (hash-ref sym-set-hash v) #f)))))))
(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let* ([sym-set-hash (dp-set-S the-sym-set)]
            [complete-sol
             (r:complete-solution
              a-sol
              ; could have potential optimization
              (remove-duplicates
               (apply append (map r:symbolics (hash-values sym-set-hash)))))])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (r:evaluate
                           (hash-ref sym-set-hash v) complete-sol)))))))


; set type for static checking

; type object representing Set
(begin-for-syntax
  (provide
   tSetOf)

  ; underlying type object of SetOf
  (struct ty-Set (el-type) #:transparent ; set-∈ of nested set does not match
    #:property prop:type-interface (list (r:cons 'set r:identity))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'SetOf)
        (λ (self) (list (ty-Set-el-type self)))))]
    )

  ; return #f if a-t is not a subtype of the type "a set of something"
  (define (as-ty-Set a-t)
    (and
     (interfaced-type? a-t)
     ; get a function always return #f when a-t does not have a interpretation
     ; as a set type
     ((cdr (or (assoc 'set (get-type-interface a-t))
               (cons '() (const #f))))
      a-t)))

  (define-match-expander tSetOf
    (syntax-parser
      ; if the type being matched has a interpretation as tSet
      [(_ ty-el) #'(app as-ty-Set (ty-Set ty-el))])
    ; used as the constructor for the type object outside ```match'''
    (syntax-parser
      [(_ el-type) #'(ty-Set el-type)]))
)


; set-like structure
; Note: dp-set? implies dp-set/c
;       contract for S is assumed as invariant except for using (dp-set #f) as null set
; (SOLVED) XXX: currently, two dp-set are equal? iff both the ground set and members are equal
;
; the set of keys is the ground set, keys mapped to #t are the actual members
;
; S : (hash/c any/c boolean?)

; fallback to use Racket struct avoid Rosette symbolic evaluation opening up the structure
; resulting fields of the structure becoming unions
; Note: defining ``gen:equal+hash'' seemed to prevent this
(struct dp-set (S)
          ; why ```prop:interface ('a)''' passes compilation
          #:property prop:interface
                    (r:list
                       (r:cons 'set r:identity); casting to set is identity
                       (r:cons 'symbolic?
                               (λ (the-set)
                                 (r-symbolic-atom?
                                  (hash-iterate-value
                                   (dp-set-S the-set)
                                   (hash-iterate-first (dp-set-S the-set))
                                   #f))))
                     ) 
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-set port mode)
                 (if (dp-set-S the-set)
                     (if (list? (dp-set-members->list the-set))
                         (fprintf port "{~a}" (string-join (map
                                                            (λ (e) (format "~s" e))
                                                            (dp-set-members->list the-set)) ", "))
                         (begin
                           (print "dp-set:" port)
                           (print (dp-set-S the-set) port)))
                     (fprintf port "null (no solution)"))))]
          #:methods gen:equal+hash
          [(define equal-proc set-equal?)
           (define (hash-proc a-set recursive-equal-hash)
             (equal-hash-code (dp-set-S (dp-set-shrink a-set))))
           (define (hash2-proc a-set recursive-equal-hash)
             (equal-secondary-hash-code (dp-set-S (dp-set-shrink a-set))))]
          #:methods gen:dp-mergeable
                    ; S-ref is the representative set, which should have completed all keys
                    ; i.e. the union of all hash keys of the underlying hashes of the components
                    ; of the symbolic union
                    [(define (gen-merge-union U-sets S-ref)
                       (let ([H (dp-set-S S-ref)])
                         (dp-set (for/hash ([k (hash-keys H)])
                                   (values k (r:for/all ([Sx U-sets])
                                                        (hash-ref (dp-set-S Sx) k #f)))))))                     
                     (define (gen-representative-el-from-lst S-lst dummy-set)
                       (dp-set (for/hash
                                   ([k (apply append
                                              (map (λ (a-set) (hash-keys (dp-set-S a-set)))
                                                   S-lst))])
                                 (values k #t))))                     
                     (define gen-decode-merged-from-sol dp-set-from-sol)]
          #:transparent)

; null set
; used to represent no solution
(define dp-null-set (dp-set #f))

; contract for object that can be interpret as a set (set-like)
; an-object : any/c
; -> boolean?
(define (dp-set/c an-object)
  (not (not ; convert to boolean?
    (and
     (interfaced-struct? an-object)
     (assoc 'set (get-interface an-object))))))

; contract combinator for set-like with members satisfying given contract, internal
; Note: flat version, membering element contracts are also flat
;       used to check only structure without value dependency
;       e.g. ``Are the members a set of integer?''
;       but not ``Are the members subset of another value?''
; el-ctc : (-> any/c boolean?), contract of the membering element
; -> (any/c -> boolean?)
(define (dp-setof/c el-ctc) ; curried shorthand
  (make-flat-contract
   #:name 'set-like
   #:late-neg-projection
   (λ (blame)
     (define el-proj ((contract-late-neg-projection el-ctc)
                      (blame-add-context blame (format "an element of" ))))
     (λ (an-object neg-party)
       (if (interfaced-struct? an-object)
           (let ([to-set (assoc 'set (get-interface an-object))])
             (if to-set
                 (let ([the-hash (dp-set-S ((cdr to-set) an-object))])
                   (map
                    (λ (e)
                      ; enforce [ e ∈ S => (el-ctc e) is #t ]
                      (if (hash-ref the-hash e)
                          (el-proj e neg-party) ; error triggered here if violation
                          e))
                    (hash-keys the-hash)) ; result discarded
                   an-object)
                 (raise-blame-error blame #:missing-party neg-party
                                    an-object '(expected "an object interpretable as a set" given: "~e") 
                                    an-object)))
           (raise-blame-error blame #:missing-party neg-party
                              an-object '(expected "an object interpretable as a set" given: "~e") 
                              an-object))
       ))))

; construct a contract factory for contract of set-like with members satisfying
; specific contracts, internal
; Note: value-dependent version, produce a factory accepting dependent values
;       The factory generates contracts that check members satisfying certain property
;       dependent on values feed to the factory. But the generated contract does not
;       check the value-dependent properties that set satisfies as a whole.
;       e.g., it can check ``Are the members subset of another value?''
;             (by passing another contract factory that accepts a super set S (another value)
;             and generate a contract taking a set T returns if T ⊂ S)
;             but not ``Is this set a family of subset of another value?''
; el-ctc-d : (-> any/c ... (-> any/c boolean?)), contract of the membering element
; -> (-> any/c ... (any/c -> boolean?))
(define ((dp-setof-d/c el-ctc-d) v . rest) ; curried shorthand
    ; produce contract of elements given dependent values
    (let ([el-ctc (apply el-ctc-d (cons v rest))])
      (make-flat-contract
       #:name 'set-like
       #:late-neg-projection
       (λ (blame)
         (define el-proj ((contract-late-neg-projection el-ctc)
                          (blame-add-context blame (format "an element of" ))))
         (λ (an-object neg-party)
           (if (interfaced-struct? an-object)
               (let ([to-set (assoc 'set (get-interface an-object))])
                 (if to-set
                     (let ([the-hash (dp-set-S ((cdr to-set) an-object))])
                       (map
                        (λ (e)
                          ; enforce [ e ∈ S => (el-ctc e) is #t ]
                          (if (hash-ref the-hash e)
                              (el-proj e neg-party) ; error triggered here if violation
                              e))
                        (hash-keys the-hash)) ; result discarded
                       an-object)
                     (raise-blame-error blame #:missing-party neg-party
                                  an-object '(expected "an object interpretable as a set" given: "~e") 
                                  an-object)))
               (raise-blame-error blame #:missing-party neg-party
                                  an-object '(expected "an object interpretable as a set" given: "~e") 
                                  an-object))
           )))
      ))

; return a contract checking the set size of a set is exactly n
(define (dp-set-size=/c n)
  (make-flat-contract
   #:name 'set-size
   #:late-neg-projection
   (λ (blame)
     (λ (a-set neg-party)
       ; alternatively: use dp-equal? to wrap raw int if present
       (if (equal? (dp-int-unwrap (set-size a-set))
                   (dp-int-unwrap n))
           a-set
           (raise-blame-error blame #:missing-party neg-party
                              a-set '(expected "a set of size ~e" given: "~e")
                              n
                              a-set))))))

; convert set-like to set, raise error otherwise
; an-object : any/c
; -> dp-set?
(define (as-set an-object)
  (r:if (r:and
         (interfaced-struct? an-object)
         (r:assoc 'set (get-interface an-object)))
        ((r:cdr (r:assoc 'set (get-interface an-object))) an-object)
        (error "can not be used as a set:" an-object)))

; covert the ground set of a set-like to Racket list, internal
; a-set : dp-set/c
; -> list?
(define (dp-ground-set->list a-set)
  (let ([S (dp-set-S (as-set a-set))])
    (if S
        (hash-keys S)
        '())))

; create a new set with elements
; elements : list?
; -> dp-set?
(define (a-set . elements)
  (dp-set (make-immutable-hash
           (r:map
            (r:λ (e)
                 (r:cons
                  (if (dp-symbolic? e)
                      (raise "can not add an element whose value is to be solved to the set")
                      e) #t))
            elements))))

; FIXME
#;(define (make-set a-set el-type)
  (let ([the-set (as-set a-set)])
    (make-immutable-hash
     (r:map
      (r:λ (e) (r:cons (struct el-type e) #t))
      (hash-keys (dp-set-S the-set))))))


; begin
; for debugging
#;(begin-for-syntax
  (define-match-expander testB
    (syntax-parser
      [_ #'1])
    (syntax-parser
      [_ #'1])))
#;(define-syntax test1
  (tBool))
; end of debugging

; check if a-element is a member of a-set
; a-element : any/c
; a-set : dp-set/c

(provide set-∈-typed-rewriter
         set-∉-typed-rewriter)
(define-syntax set-∈-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON τb) (_ (tSetOf τb)))
       (λ (stx) (cons stx (tBool)))]
      [(args-τ ('SYM τb) (_ (tSetOf τb)))
       (syntax-parser
         [(set-∈ arg-el arg-S)
          (cons #'(set-∈-safe arg-el arg-S) (tBool))])]
      [(args-τ (_ τb0) (_ (tSetOf τb1)))
       (syntax-parser
         [(set-∈ arg-el arg-S) (raise-syntax-error #f "element type does not match the set"
                                                   #'(set-∈ arg-el arg-S)
                                                   #'arg-el)])]
      [(args-τ (_ _) (_ _))
       (syntax-parser
         [(set-∈ arg0 arg1) (raise-syntax-error #f "expects a set"
                                                   #'(set-∈ arg0 arg1)
                                                   #'arg1)])]
      [_ (λ (stx) (raise-syntax-error #f "expect 2 arguments" stx))])))

(define-syntax set-∉-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON τb) (_ (tSetOf τb)))
       (λ (stx) (cons stx (tBool)))]
      [(args-τ ('SYM τb) (_ (tSetOf τb)))
       (syntax-parser
         [(set-∉ arg-el arg-S)
          (cons #'(set-∉-safe arg-el arg-S) (tBool))])]
      [(args-τ (_ τb0) (_ (tSetOf τb1)))
       (syntax-parser
         [(set-∉ arg-el arg-S) (raise-syntax-error #f "element type does not match the set"
                                                   #'(set-∉ arg-el arg-S)
                                                   #'arg-el)])]
      [(args-τ (_ _) (_ _))
       (syntax-parser
         [(set-∉ arg0 arg1) (raise-syntax-error #f "expects a set"
                                                   #'(set-∉ arg0 arg1)
                                                   #'arg1)])]
      [_ (λ (stx) (raise-syntax-error #f "expect 2 arguments" stx))])))

; concrete versions, unsafe when a-element contains symbolic value
(define (set-∈ a-element a-set)
  (hash-ref (dp-set-S (as-set a-set)) (dp-wrap-if-raw-int a-element) #f))
(define (set-∉ a-element a-set)
  (r:not (set-∈ a-element a-set)))
; safe versions
(define (set-∈-safe a-element a-set)
  (∃ [v ∈ (as-set a-set)]
     (dp-equal? a-element v)))
(define (set-∉-safe a-element a-set)
  (∀ [v ∈ (as-set a-set)]
     (r:not
      (dp-equal? a-element v))))
; fallback to safe version only when a-element is symbolic
; not in use
#;(define (set-∈ a-element a-set)
  (if (dp-symbolic? a-element)
      (set-∈-safe a-element a-set)
      (set-∈-con a-element a-set)))
#;(define (set-∉ a-element a-set)
  (if (dp-symbolic? a-element)
      (set-∉-safe a-element a-set)
      (set-∉-con a-element a-set)))

; convert Racket list to a hash with each key maps to #t, internal
; -> (hash/c any/c boolean? ....)
(define (dp-list->hash a-lst)
  (make-immutable-hash
   (r:map
    (r:λ (e) (r:cons e #t))
    a-lst)))

; convert Racket list to a set, internal
; a-lst : list?
; -> dp-set?
(define (dp-list->set a-lst)
  (dp-set (dp-list->hash
           a-lst)))

; build a set with members mbr-lst and potential members pmbr-lst,
; internal, non-solvable
; Note: resulting ground set will be mbr-lst union pmbr-lst
; mbr-lst : list?
; pmbr-lst : list?
; -> dp-set?
(define (dp-list-list->set mbr-lst pmbr-lst)
  (dp-set (make-immutable-hash
           (map
            (λ (e) (cons e (if (member e mbr-lst) #t #f)))
            (append mbr-lst pmbr-lst)))))

; get the ground set of a set-like
; a-set : dp-set/c
; -> dp-set?
(define (set-ground-set a-set)
  (dp-set (make-immutable-hash
           (r:map
            (r:λ (e) (r:cons e #t))
            (hash-keys
             (dp-set-S (as-set a-set)))))))

; get rid of nonmember ground set elements of a set-like, internal,
; non-solvable(!) (r:filter may generate symbolic hash,
;                    not work with hash-ref (?) )
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-shrink a-set)
  (let ([the-set-hash (dp-set-S (as-set a-set))])
    (dp-set (for/hash ([e (hash-keys the-set-hash)]
                       #:when (hash-ref the-set-hash e))
              (values e #t)))))

; get the set members of a set-like as Racket list, internal
; non-solvable(!) (r:filter may generate symbolic hash,
;                    not work with hash-ref (?) )
; a-set : dp-set/c
; -> list?
(define (dp-set-members->list a-set)
  (r:let ([the-set-hash (dp-set-S (as-set a-set))])
    (r:filter (r:λ (e) (hash-ref the-set-hash e #f))
              (hash-keys the-set-hash))))

; check if set-a is a subset of set-b
; set-a : dp-set/c
; set-b : dp-set/c
; -> boolean?
(define (set-subset-of? set-a set-b)
  (r:let ([the-set-hash-a (dp-set-S (as-set set-a))]
          [the-set-hash-b (dp-set-S (as-set set-b))])
         (r:andmap (r:λ (e)
                        (r:implies
                         (hash-ref the-set-hash-a e #f)
                         (hash-ref the-set-hash-b e #f)))
                   (hash-keys the-set-hash-a))))
(kv-func-type-annotate set-subset-of? ((tSetOf τb) (tSetOf τb) (tBool))
                       "two sets of the same element type")

; XXX: maybe nonsolvable(?) because of the presence of remove-duplicates
; union set of the set-likes
; the ground set of the union is the union of ground sets
; a-p-set ... : dp-set/c ...
; -> dp-set?
(define-syntax (set-∪ stx)
  (syntax-parse stx
    [(_ a-set-like ...)
     #:with (the-set ...) (generate-temporaries #'(a-set-like ...))
     #:with (a-gnd-set ...) ; ground sets represented as lists of hash-keys
     (r:map
      (r:λ (s)
           #`(hash-keys (dp-set-S #,s)))           
      (syntax->list #'(the-set ...)))
     #'(r:let ([the-set (as-set a-set-like)] ...) ; caching casting to set
        (dp-set
         (make-immutable-hash
          (r:map
           (r:λ (e)
               (r:cons
                e
                (r:ormap
                 (r:λ (s) ; set-like
                      (hash-ref (dp-set-S s) e #f))
                 (r:list the-set ...))))
           (r:remove-duplicates (r:append a-gnd-set ...))))))])) ; maybe don't remove duplicate here?
(kv-func-type-annotate set-∪ ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element-type")


; intersection set of the set-likes
; the ground set of the intersection is the of ground set of the first set
; Note: since we don't have the universe set (identity element for intersection),
;       set-∩ must be supplied with at least 1 element
; a-p-set ...+ : dp-set/c ...
; -> dp-set?
(define-syntax (set-∩ stx)
  (syntax-parse stx
    [(_ a-set-like0 a-set-like1 ...)
     #:with (s1 ...) (generate-temporaries #'(a-set-like1 ...))
     #'(let ([s0 (as-set a-set-like0)]
             [s1 (as-set a-set-like1)] ...)
         (dp-set
          (make-immutable-hash 
           (r:map
            (r:λ (k)
                 (cons
                  k
                  (r:and (hash-ref (dp-set-S s0) k #f)
                         (hash-ref (dp-set-S s1) k #f) ...)))
            (hash-keys (dp-set-S s0))))))]))
(kv-func-type-annotate set-∩ ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element-type")

; remove an element from a set
; non-sets are converted to sets,
; nothing observable happens if the element is not in the set
; Note: may strips the chaperone if a-set is chaperoned
;       non-solvable(?) if the element is symbolic,
;       i.e., if the value depends on other symbolic value
;       so make it internal at least now
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-remove a-set e)
  (dp-set (hash-set (dp-set-S (as-set a-set)) e #f)))

; select the subset of a set satisifying pred
; internal, see below
; Note: All e in the ground set will be fed to pred.
;       There will be a problem if anything in the
;       ground set that is not compatible with pred.
; pred : (-> any/c boolean?)
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-filter pred a-set)
  (let ([the-set-hash (dp-set-S (as-set a-set))])
   (dp-set
    (make-immutable-hash
     (r:map
      (r:λ (e)
           (r:cons e
                   (r:if (hash-ref the-set-hash e #f)
                         (pred e)
                         #f)))
      (hash-keys the-set-hash))))))

; the set diffence of two set-like
; set-a : dp-set/c
; set-b : dp-set/c
; -> dp-set?
(define (set-minus set-a set-b)
  (dp-set
   (make-immutable-hash
    (r:let ([the-set-hash-a (dp-set-S (as-set set-a))]
            [the-set-hash-b (dp-set-S (as-set set-b))])
           (r:map
            (r:λ (x)
                 (r:cons
                  x
                  (r:and
                   (hash-ref the-set-hash-a x #f)
                   (r:not (hash-ref the-set-hash-b x #f)))))
            (hash-keys the-set-hash-a))))))
(kv-func-type-annotate set-minus ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element type")

; calculate the number of members in the set
; a-set : dp-set/c
(define (set-size a-set)
  (r:let ([the-set-hash (dp-set-S (as-set a-set))])
    (dp-integer
     (r:count
      (r:λ (v) (hash-ref the-set-hash v #f))
      (hash-keys the-set-hash))
     ; XXX: unforunately for now we can not tell if the set is constant or not
     ;      assign the size to ;poly for safety
     'poly)))
(kv-func-type-annotate set-size ((tSetOf τb) (tInt))
                       "a set")

(kv-func-type-annotate different? (τb τb (tBool))
                       "two objects of the same type")
(kv-func-type-annotate equal? (τb τb (tBool))
                       "two objects of the same type")


; create a solvable symbolic subset of ground-set, internal, non-solvable(?)
; ground-set : dp-set/c
; -> (dp-setof/c symbolic?)
(define (dp-symbolic-subset ground-set [size #f])
  (values
   (let ([members (dp-set-members->list ground-set)])
    (dp-set (for/hash ([e members])
              (values e (fresh-symbolic-bool)))))
   (if size
       (r:list (r:λ (a-set)
                   (r:equal? (set-size a-set) size)))
       '())))

; null set
; used to represent no solution
#;(define dp-null-set (dp-set #f))

; get the solved set from the rosette solution
; a-sol : r:solution? 
; the-sym-set : (), assumed to be consistent with the solution
#;(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let ([sym-set-hash (dp-set-S the-sym-set)])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (hash-ref (r:model a-sol)
                                    (hash-ref sym-set-hash v) #f)))))))


;
; tuple definition and operations
;

(provide
 (struct-out dp-tuple)
 fst
 snd
 trd
 frh
 ffh
 n-th
 tpl

 tuple)

; type object representing Tuple
(begin-for-syntax
  (provide tTuple)

  (struct ty-Tuple (type-lst)
    #:property prop:type-interface (list (r:cons 'tuple r:identity))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Tuple)
        (λ (self) (ty-Tuple-type-lst self))))])

  (define (as-ty-Tuple a-t)
    (and
     (interfaced-type? a-t)
     ; get a function always return #f when a-t does not have a interpretation
     ; as ty-Tuple
     ((cdr (or (assoc 'tuple (get-type-interface a-t))
               (cons '() (const #f))))
      a-t)))
  
  (define-match-expander tTuple
    (syntax-parser
      [(_ el-type0 el-type ...)
       #'(app as-ty-Tuple (ty-Tuple (list el-type0 el-type ...)))])
    ; used as the constructor for type object outside ```match'''
    (syntax-parser
      [(_ #:list lst) #'(ty-Tuple lst)]
      [(_ el-type0 el-type ...) #'(ty-Tuple (list el-type0 el-type ...))]))

)

; fallback to Racket
; see also : dp-set
; TODO : make underlying representation of symbolic tuple
;        conform with mappings
(struct dp-tuple (lst) #:transparent
          #:property prop:interface
                    (r:list
                       (r:cons 'set
                               (r:λ (tpl)
                                    (dp-list->set (dp-tuple-lst tpl)))))
          #:methods gen:custom-write
          [(define write-proc
             (r:λ (the-tuple port mode)
                  (fprintf port "~a"
                           (dp-tuple-lst the-tuple))))])
; XXX: element accessors of the tuple might not support
;      symbolic tuples at this point
(define (fst a-tuple)
  (r:first (dp-tuple-lst a-tuple)))
(kv-func-type-annotate fst ((tTuple τb1 τb2 ...) τb1)
                       "a tuple")

(define (snd a-tuple)
  (r:second (dp-tuple-lst a-tuple)))
(kv-func-type-annotate snd ((tTuple τb1 τb2 τb3 ...) τb2)
                       "a tuple")

(define (trd a-tuple)
  (r:third (dp-tuple-lst a-tuple)))
(kv-func-type-annotate trd ((tTuple τb1 τb2 τb3 τb4 ...) τb3)
                       "a tuple of at least 3 elements")

(define (frh a-tuple)
  (r:fourth (dp-tuple-lst a-tuple)))
(kv-func-type-annotate frh ((tTuple τb1 τb2 τb3 τb4 τb5 ...) τb4)
                       "a tuple of at least 4 elements")

(define (ffh a-tuple)
  (r:fifth (dp-tuple-lst a-tuple)))

(define (n-th a-tuple n)
  (r:list-ref (dp-tuple-lst a-tuple) n))

(define (dp-tuple/c . el-ctcs)
  (struct/c dp-tuple
            (apply list/c el-ctcs)))

; construct a contract factory for contract of tuple
; internal
; Note: value-dependent version, produce a factory accepting dependent values
; See also: dp-setof-d/c
; el-ctc-d : (-> any/c ... (-> any/c boolean?)), contract of one of the element
; ......
; -> (-> any/c ... (any/c -> boolean?))
(define ((dp-tuple-d/c . el-ctcs-d) v . rest)
  (λ (a-tuple)
   (andmap
    (λ (i)
      ((apply (list-ref el-ctcs-d i) (cons v rest))
       (list-ref (dp-tuple-lst a-tuple) i)))
    (range (length (dp-tuple-lst a-tuple))))))

; tuple constructor
(define (tpl v . rest)
  (dp-tuple (cons v rest)))

; create the cartisan product of sets
; ∀(dp-setof/c α) ... -> (dp-setof/c (dp-tuple/c α) ...)
; potentially expensive, internal, nonsolvable
(define (dp-set-product . rest)
  (dp-list->set
   (map
    dp-tuple
    (apply cartesian-product
           (map
            dp-set-members->list
            rest)))))




; for generating random instance field
(require racket/random)



(provide [for-syntax
          ; syntax class for parsing aggregations
             element-of-a-set
             element-of-product-of-2-sets])

(begin-for-syntax
  
  (define-syntax-class element-of-a-set
    #:datum-literals (∈ in)
    #:description "an element from a set"
    (pattern [x:id (~or ∈ in) X:expr]))

  (define-syntax-class element-of-product-of-2-sets
    #:datum-literals (∈ in × * where)
    #:description "a pair from a set"
    (pattern [(x:id y:id)
              (~or ∈ in) (X:expr (~or × *) Y:expr)
              where x-y-pred?:expr]))
  
)


; don't care element type of a set or tuple (accepts anything)
(define-syntax (dont-care stx)
  (if (dp-parse-table)
      ; only valid for inst
      (if (not (dp-part-cert-env?))
          (dp-stx-type-desc
           (generate-temporary #'dont-care)
           type 'dont-care
           kv-type-object #'(tSymbol) ; use as syntax object to avoid 3d-syntax
           atomic? #f ; because you don't know what's inside, e.g. might be sets
           ctc #'any/c
           v-dep-ctc #'v-dep-any/c
           type-data '()
           accessors '()
           generator #`(λ (a-inst) ; the instance can be incomplete
                         (λ () (gen-random-sym-el '#,(dp-cur-field-id)))))
          (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (raise-syntax-error 'dont-care "unsupported" stx)))

; (Discarded, not updated to work with the type system)
; generate a struct, current design shifts away from it
; specific element type of a set 
(define-syntax (element stx)
  (if (dp-parse-table)
      ; only valid for inst
      (if (not (dp-part-cert-env?))
          (syntax-parse stx
            [(_ #:type-name type-name:id (~optional (~seq #:attributes (element-attr:id ...+))))
             #:with stx-id (generate-temporary #'element)
             #:with ctc-id (format-id #'stx-id "~a/c" #'stx-id)
             (dp-stx-type-desc #'stx-id
                               type 'element
                               atomic? #f
                               ctc #'ctc-id
                               v-dep-ctc #'v-dep-any/c
                               el-type-to-make (hash 'type-name #'type-name
                                                     'placeholder #'ctc-id
                                                     'attrs (if (attribute element-attr)
                                                                (syntax->list #'(element-attr ...))
                                                                '()))
                               type-data '()
                               accessors '())])
          (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (raise-syntax-error 'element unsupport-outside-problem-definition-msg stx)))


; S1 setof element
; S2 setof subset-of S1
; (setof (λ(s) (subset-of? S1)))


; generate random set
; el-gen : ∀α . (-> (listof α) α)
; el-gen generate a new element
; XXX: magic number
(define (gen-random-set el-gen #:size [size #f])
  (let ([size (dp-int-unwrap (if size size (random 6 13)))])
    (let rec ([cur '()]
              [k size]
              [cnt 0])
      (cond [(equal? k 0) (dp-list->set cur)]
            ; time out after some trials for each element
            [(>= cnt 10) (error "failed to generate set satisfying invariants before timed out")]
            [else (let ([the-el (el-gen)])
                    (if (member the-el cur)
                        (rec cur k (+ cnt 1))
                        (rec (cons the-el cur) (- k 1) 0)))]))
    ))


; set
(define-syntax (set stx)
  (if (dp-parse-table)
      (if
       ; only valid in inst enviroment
       (not (dp-part-cert-env?))
       (syntax-parse stx
         [(_ (~optional (~seq #:of-type type-desc))
             (~optional (~seq #:size size)))
          (let* ([el-type
                  (dp-stx-type-desc
                   (dp-expand-part
                    (if (attribute type-desc)
                        #'type-desc
                        #'dont-care)))]
                 ; (not maybe-size) => size not specified
                 ; (and maybe-size (not size-as-num)) => size specified as variable
                 [maybe-size (if (attribute size) #'size #f)]
                 [size-as-num
                  (get-size-as-num maybe-size)]
                 [el-ctc (dp-stx-info-field el-type ctc)]
                 [el-v-dep-ctc (dp-stx-info-field el-type v-dep-ctc)]
                 [set-ctc
                  (if size-as-num
                      #`(make-flat-contract
                         #:name '-subset
                         #:late-neg-projection
                         (λ (blame)
                           (λ (a-set neg-party)
                             ; use dp-equal? to wrap raw int if present
                             (if (dp-equal? (set-size a-set) #,size-as-num)
                                 (((contract-late-neg-projection (dp-setof/c #,el-ctc)) blame)
                                  a-set neg-party)             
                                 (raise-blame-error blame #:missing-party neg-party
                                                    a-set
                                                    '(expected "a set of size ~e" given: "~e")
                                                    #,size-as-num
                                                    a-set)))))
                      #`(dp-setof/c #,el-ctc))]
                 [set-v-dep-ctc
                  (if (and maybe-size (not size-as-num))
                      #`(λ (a-inst)
                          (make-flat-contract
                           #:name '-subset
                           #:late-neg-projection
                           (λ (blame)
                             (define el-ctc ((dp-setof-d/c #,el-v-dep-ctc) a-inst))
                             (λ (a-set neg-party)
                               ; use dp-equal? to wrap raw int if present
                               (if (dp-equal? (set-size a-set) #,(instance-field-ref #'a-inst maybe-size))
                                   (((contract-late-neg-projection el-ctc) blame)
                                    a-set neg-party)             
                                   (raise-blame-error blame #:missing-party neg-party
                                                      a-set
                                                      '(expected "a set of size ~e" given: "~e")
                                                      #,(instance-field-ref #'a-inst maybe-size)
                                                      a-set))))))
                                   
                      #`(dp-setof-d/c #,el-v-dep-ctc))]
                 ; ids in referred parts
                 [type-desc-ids (dp-stx-info-field el-type referred-ids '())])
            (dp-stx-type-desc (generate-temporary #'set)
                              type 'set
                              kv-type-object #`(tSetOf
                                                #,(dp-stx-info-field el-type kv-type-object))
                              ;test (raise-syntax-error #f "here")
                              atomic? #f
                              ctc set-ctc
                              v-dep-ctc set-v-dep-ctc
                              el-type-to-make (dp-stx-info-field el-type el-type-to-make)
                              type-data (list (cons 'el-type el-type)
                                              (cons 'size maybe-size))
                              accessors (list (cons 'set #'identity))
                              generator #`(λ (a-inst)
                                            (λ ()
                                              (gen-random-set
                                               (#,(dp-stx-info-field el-type generator) a-inst)
                                               #:size #,(if (and maybe-size (not size-as-num))
                                                            (instance-field-ref #'a-inst maybe-size)
                                                            size-as-num))))
                              referred-ids (if (and maybe-size
                                                    (not size-as-num))
                                               (cons maybe-size type-desc-ids)
                                               type-desc-ids)))]
         [_:id #'(set)])
       (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (syntax-parse stx
        ; XXX: temporary solution, probably non-solvable(?)
        ; better use another name that is not available for individual problem definition
        #;[(_ [x-expr (~datum for) x-in-X:element-of-a-set
                    (~optional (~seq (~datum if) pred-x))])
         ; the code below try to create the key of the resulting hash in the set
         ; without adding or removing symbols. However, if the elements of the X or
         ; x-expr are sets, which contains hash-tables, this could resulting hash symbolic hash tables
         #`(r:map
              (r:λ (x-in-X.x)
                   (r:if
                    (r:and (set-∈ x-in-X.x x-in-X.X)
                           #,(if (attribute pred-x) #'pred-x #t))
                    x-expr)
                   x-in-X.x)
              (dp-ground-set->list x-in-X.X))]
        ; set literal
        [(_ elements ...)
         #'(a-set (dp-wrap-if-raw-int elements) ...)])))

(define-syntax (the-set-of stx)
  (raise-syntax-error #f unsupport-outside-problem-definition-msg stx))

(define-syntax (the-product-of stx)
  (if (dp-parse-table)     
      (syntax-parse stx
        [(_ set-name-or-desc ...+)
         (let*
             ([sets-lst (stx->list #'(set-name-or-desc ...))]
              [set-types
               (map
                (λ (a-stx origin-stx)
                  (if (dp-stx-type-info a-stx) ; alternatively: (not (identifier? origin-stx))
                      ; expanded to stx obj with type-info stx-prop attached, hence not a set name
                      (if (equal? (dp-stx-type-info-data-ref a-stx 'el-type) 'undefined)               
                          (raise-syntax-error
                           #f
                           "not a set value"
                           origin-stx)
                          ; return the syntax object with type-info directly
                          a-stx)
                      ; ``a-stx'' (and ``origin-stx'' as well) is an id, giving the set name
                      (let ([set-entry (free-id-table-ref (dp-parse-table) a-stx #f)])
                        (if set-entry
                            (let ([set-entry-type (parsed-entry-type set-entry)])
                              (if (equal? (dp-stx-type-info-data-ref
                                           set-entry-type
                                           'el-type)
                                          'undefined)
                                  ; a set-like must have ``element type'' in type-info
                                  (raise-syntax-error
                                   #f
                                   "not a valid set"
                                   origin-stx)
                                  set-entry-type))
                            (raise-syntax-error #f "undefined set instance field" a-stx)))
                      ))
                (dp-expand-parts
                 #'(set-name-or-desc ...)) sets-lst)]
              [el-types (map (λ (a-type-info) (dp-stx-type-info-data-ref a-type-info 'el-type)) set-types)]
              [el-kv-type-objects
               (map (λ (a-type-info)
                      (dp-stx-info-field a-type-info kv-type-object))
                    el-types)]
              [el-ctcs (map (λ (a-type-info) (dp-stx-info-field a-type-info ctc)) el-types)]
              [el-v-dep-ctcs (map (λ (a-type-info) (dp-stx-info-field a-type-info v-dep-ctc)) el-types)]
              [el-ctc #`(dp-tuple/c #,@el-ctcs)]
              [el-v-dep-ctc #`(dp-tuple-d/c #,@el-v-dep-ctcs) ]
              [upstream-lst (map
                             (λ (i)
                               (if (identifier? (list-ref sets-lst i))
                                   (list-ref sets-lst i)
                                   (dp-stx-type-info (list-ref set-types i))))
                             (range (length sets-lst)))]
              [upstream-accessor-lst (map
                                      (λ (a-set-type)
                                        (dp-stx-type-info-accessor-ref a-set-type 'set))
                                      set-types)]
              [upstream-ids (apply
                             append
                             (map
                              (λ (i)
                                (append
                                 (if (identifier? (list-ref sets-lst i))
                                     (list (list-ref sets-lst i))
                                     '())
                                 (dp-stx-type-info-field (list-ref set-types i) referred-ids '())))
                              (range (length sets-lst))                             
                              ))])
           (dp-stx-type-info
            (generate-temporary #'the-product-of)
            type 'set
            kv-type-object #`(tSetOf (tTuple #,@el-kv-type-objects))
            atomic? #f
            ctc #'(dp-setof/c any/c)
            v-dep-ctc #`(dp-setof-d/c v-dep-any/c)
            upstream upstream-lst
            upstream-accessor upstream-accessor-lst
            upstream-combinator #'dp-set-product
            type-data (list (cons 'el-type
                                  (dp-stx-info
                                   type 'tuple
                                   kv-type-object #`(tTuple #,@el-kv-type-objects)
                                   atomic? #f
                                   ctc el-ctc
                                   v-dep-ctc el-v-dep-ctc
                                   type-data '()
                                   accessors '())))
            accessors (list (cons 'set #'identity))
            referred-ids upstream-ids))])
      (raise-syntax-error #f unsupport-outside-problem-definition-msg stx)))

(provide random-subset)
(define (random-subset S n #:exact-n? [replacement? #t])
  (let ([n (dp-int-unwrap n)])
    (if (> n (dp-int-unwrap (set-size S)))
        (error "not enough element in the set")
        (let ([l (dp-set-members->list S)])
          (dp-list->set (random-sample l n #:replacement? replacement?))))))

(define-syntax (dp-make-flat-contract stx)
  (syntax-parse stx
    [(_ () ...+)
     #`()]))

(define-syntax (subset-of stx)
  (if (dp-parse-table)     
      (syntax-parse stx
        [(_ ((~literal the-set-of) type-desc))
         #'(set #:of-type type-desc)]
        ;-------------------------------
        #;[(_ ((~literal the-product-of) set-desc ...+))
         #:with (kw-ft ...) (make-list (length (stx->list #'(set-desc ...))) #'#:field-type)
         #:with (field-type ...) (map (λ (a-stx)
                                        (if (identifier? a-stx)
                                            #`(element-of #,a-stx)
                                            a-stx))
                                      (stx->list #'(set-desc ...)))
         #'(set #:of-type (tuple (~@ kw-ft field-type) ... ))]
        #;[(_ ((~literal the-product-of) (~or set-name:id set-desc) ...+))
         #:with (field-type ...) #'((~? set-desc (element-of set-name)) ...)
         #:with (kw-ft ...) (make-list (length (stx->list #'(field-type ...))) #'#:field-type)
         #'(set #:of-type (tuple (~@ kw-ft field-type) ... ))]
        ;-------------------------------
        ; use the following alternative
        [(_ (~or superset-name:id setlike-value)
            (~optional (~seq #:size size)))
         (let*
             ([superset-temp-name
               (if (attribute superset-name)
                   #'superset-name
                   (generate-temporary))]
              [maybe-parsed-setlike-value
               (if
                ; matched non-id as setlike-value
                (attribute setlike-value)
                (let
                    ([parsed-part
                      (dp-expand-part #'setlike-value)])
                  (if (equal? (dp-stx-type-info-data-ref parsed-part 'el-type) 'undefined)               
                      (raise-syntax-error
                       #f
                       "not a set value"
                       #'setlike-value)
                      parsed-part))
                #f)]
              [parsed
               (if maybe-parsed-setlike-value
                   (parsed-table-with-temp-field
                    superset-temp-name
                    maybe-parsed-setlike-value)
                   ; supposed to be working the same as following
                   ;-----
                   #;(free-id-table-set
                      (dp-parse-table)
                      superset-temp-name
                      (cons maybe-parsed-setlike-value #f))
                   ;-----
                   (dp-parse-table))]
              [super-set-entry (free-id-table-ref parsed superset-temp-name #f)]
              [super-set-type
               (if super-set-entry
                   (parsed-entry-type super-set-entry)
                   (raise-syntax-error
                    #f
                    "undefined superset"
                    #'superset-name))]
              [super-set-idx
               (parsed-entry-idx super-set-entry)]
              [parsed-el-type
               (let ([super-el-type (dp-stx-type-info-data-ref
                                     super-set-type
                                     'el-type)])
                 (if (equal? super-el-type 'undefined)
                     ; a set-like must have ''element type'' in type-info
                     (raise-syntax-error
                      #f
                      "not a valid superset"
                      superset-temp-name)
                     super-el-type))]
              [maybe-size (if (attribute size) #'size #f)]
              [size-as-num
               (get-size-as-num maybe-size)]
              [upstream (if maybe-parsed-setlike-value
                            (dp-stx-type-info maybe-parsed-setlike-value)
                            #'superset-name)]
              [upstream-accessor (dp-stx-type-info-accessor-ref super-set-type 'set)]
              [el-ctc (dp-stx-info-field parsed-el-type ctc)]
              [el-v-dep-ctc (dp-stx-info-field parsed-el-type v-dep-ctc)]
              [set-ctc (if size-as-num
                           #`(make-flat-contract
                              #:name '-subset
                              #:late-neg-projection
                              (λ (blame)
                                (λ (a-set neg-party)
                                  ; use dp-equal? to wrap raw int if present
                                  (if (dp-equal? (set-size a-set) #,size-as-num)
                                      (((contract-late-neg-projection (dp-setof/c #,el-ctc)) blame)
                                       a-set neg-party)               
                                      (raise-blame-error blame #:missing-party neg-party
                                                         a-set
                                                         '(expected "a set of size ~e" given: "~e")
                                                         #,size-as-num
                                                         a-set)))))
                           #`(dp-setof/c #,el-ctc))]
              [set-v-dep-ctc #`(λ (a-inst)
                                 (make-flat-contract
                                  #:name '-subset-v-dep
                                  #:late-neg-projection
                                  (λ (blame)
                                    ; projection for the value dependent contract of the elements
                                    (define setof-v-dep-proj
                                      ((contract-late-neg-projection
                                       ((dp-setof-d/c #,el-v-dep-ctc) a-inst))
                                       blame))
                                    (λ (a-set neg-party)
                                      (if (set-subset-of? ; subset constraint
                                           a-set
                                           ; discarded
                                           ; #; no type annotation for a-inst available yet
                                           ; #; can't refer the instance field by name accessor
                                           ; #; no way to annotate a-inst as annotation has not been generated
                                           #|(#,(let loop ([cur-layer upstream])
                                           (if (identifier? cur-layer)
                                               cur-layer
                                               #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                                  #,(loop (dp-stx-info-field cur-layer upstream)))))
                                                   a-inst)
                                            ; |#; end
                                           (#,upstream-accessor ; see also subgraph-of
                                            #,(trace-upstream-to-field upstream #'a-inst)))
                                          
                                          (if 
                                           ; size contract when size is given by an instance field
                                           #,(if (and maybe-size (not size-as-num))
                                                 ; use dp-equal? to wrap raw int if present
                                                 #`(dp-equal? (set-size a-set)
                                                           ; maybe-size is already a syntax object
                                                           #,(instance-field-ref #'a-inst maybe-size))
                                                 #'#t)
                                           ; return the projection on the value-dependent contract 
                                           (setof-v-dep-proj a-set neg-party)
                                           (raise-blame-error
                                            blame #:missing-party neg-party
                                            a-set
                                            '(expected "a set of size ~e" given: "~e")
                                            ; ``if'' is to avoid calling instance-field-ref when maybe-size
                                            ; is #f. It is not known when the code is generated.
                                            #,(if (and maybe-size (not size-as-num)) 
                                                  #`#,(instance-field-ref #'a-inst maybe-size)
                                                  #''impossible) ; this line should never reached
                                            a-set)) 
                                          (raise-blame-error blame #:missing-party neg-party
                                                             a-set
                                                             '(expected "a subset of ~e" given: "~e")
                                                             (#,upstream-accessor ; see also subgraph-of
                                                              #,(trace-upstream-to-field upstream #'a-inst))
                                                             a-set))
                                      ))))]
              ; ids referred by superset or setlike-value
              [upstream-ids (append
                             (if (attribute superset-name) (list #'superset-name) '())
                             (dp-stx-type-info-field super-set-type referred-ids '()))])
           (dp-stx-type-desc
            (generate-temporary #'set)
            type 'set
            kv-type-object #`#,(dp-stx-type-info-field super-set-type kv-type-object)
            atomic? #f
            upstream upstream
            upstream-accessor upstream-accessor
            ctc set-ctc
            v-dep-ctc set-v-dep-ctc
            type-data (list (cons 'el-type parsed-el-type)
                            (cons 'size maybe-size))
            ; accessors set : how subset-of access the object
            ; accessors vertices-of : how vertices-of access the object (not present here)
            accessors (list (cons 'set #'identity))
            generator #`(λ (a-inst)
                          (λ ()
                            (let ([superset
                                   (#,upstream-accessor
                                    #,(trace-upstream-to-field upstream #'a-inst))])
                              (random-subset
                               superset
                               #,(if maybe-size
                                     (if size-as-num
                                         size-as-num
                                         (instance-field-ref #'a-inst maybe-size))
                                     #'(random (quotient (dp-int-unwrap (set-size superset)) 2)
                                               (dp-int-unwrap (set-size superset))))
                               #:exact-n? #f))))
            ; factory (from instance) of contructor to create symbolic certificate from the object
            ; Note: the reason that returns a constructor is because this may be called by other
            ;       symbolic-constructor to create symbolic substructure
            symbolic-constructor #`(λ (a-inst)
                                     (λ ()
                                       (dp-symbolic-subset
                                        (#,upstream-accessor
                                         #,(trace-upstream-to-field upstream #'a-inst))
                                        #,(if maybe-size
                                              (if size-as-num
                                                  size-as-num
                                                  (instance-field-ref #'a-inst maybe-size))
                                              #'#f))))
            ; procedure decoding the certificate from solution object of the solver
            solution-decoder #'dp-set-from-sol
            ; null object for no solution
            null-object #'dp-null-set
            referred-ids (if (and maybe-size
                                  (not size-as-num))
                             (cons maybe-size upstream-ids)
                             upstream-ids)))])
      (raise-syntax-error #f unsupport-outside-problem-definition-msg stx)))

; tuple
(define-syntax (tuple stx)
  (if (dp-parse-table)
      (if
       ; only valid in inst enviroment
       (not (dp-part-cert-env?))
       (syntax-parse stx
         [(_ (~seq #:field-type type-desc) ...)
          (let* ([el-types
                  (map
                   (λ (a-stx) (dp-stx-type-desc a-stx))
                   (dp-expand-parts
                    #'(type-desc ...)))]
                 [el-kv-type-objects
                  (map (λ (a-type-info)
                         (dp-stx-info-field a-type-info kv-type-object))
                       el-types)]  
                 [el-ctcs (map (λ (a-stx-info) (dp-stx-info-field a-stx-info ctc)) el-types)]
                 [el-v-dep-ctcs (map (λ (a-stx-info) (dp-stx-info-field a-stx-info v-dep-ctc)) el-types)]
                 [tuple-ctc #`(dp-tuple/c #,@el-ctcs)]
                 [tuple-v-dep-ctc #`(dp-tuple-d/c #,@el-v-dep-ctcs)]
                 ; ids in referred parts
                 [type-desc-ids (apply append
                                       (map
                                        (λ (a-stx-info)
                                          (let ([a-id (dp-stx-info-field a-stx-info referred-ids)])
                                            (if (equal? a-id 'undefined)
                                                '()
                                                a-id)))
                                        el-types))])
            (dp-stx-type-desc (generate-temporary #'tuple)
                              type 'tuple
                              kv-type-object #`(tTuple #,@el-kv-type-objects)
                              atomic? #f
                              ctc tuple-ctc
                              v-dep-ctc tuple-v-dep-ctc
                              ; XXX: currently not supporting creating new element structureb
                              #;el-type-to-make #;(apply append
                                                     (map
                                                      (λ (a-stx-info)
                                                        (dp-stx-info-field a-stx-info el-type-to-make))
                                                      el-types))
                              type-data (list (cons 'el-types el-types))
                              accessors '()
                              generator #`(λ (a-inst)
                                            (apply
                                             dp-tuple
                                             #,(map
                                                (λ (el-type)
                                                  #`((#,(dp-stx-info-field el-type generator) a-inst)))
                                                el-types)))
                              referred-ids type-desc-ids))])
       (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (syntax-parse stx
        [(_ elements ...)
         #'(tpl (dp-wrap-if-raw-int elements) ...)])))

; 
; single element (of a set)
;
; Note: opaque symbolic (single) element (of a set) is represented symbolic unions
;       structures e.g. sets and mappings need to be merged
;       see also above: dp-mergeable
;

; XXX: It seems (el ) is still opened up by Rosette evaluation
;      and the substructure is merged.
;      This results a symbolic element of a set of ``el''s
;      neither a term? or union?
;      See the problem of fully-compatible for example
;
;      A temp fix is applied with
;      r:evaluate is now called on everything that is neither
;      a term? or union?


(define (evaluate-atomic-sym a-sym a-sol)
  (cond [(r:unsat? a-sol) dp-null-set]
        ;[(r:term? a-sym) (r:evaluate a-sym a-sol)]
        [(r:union? a-sym)
         (let ([l (r:union-contents a-sym)])
           (r:evaluate
            (r:cdr (assoc #t l (λ (x y)
                                 ; no order specified
                                 ; don't know whether the guard is x or y
                                 (and (r:evaluate x a-sol)
                                      (r:evaluate y a-sol)))))
            a-sol))]
        [else (r:evaluate a-sym a-sol)]))

; not in use
; extract the element from a singleton set
; (-> dp-set/c any/c)
(define (dp-extract-singleton a-set)
  (r:let ([the-hash (dp-set-S a-set)])
         (r:findf (r:λ (k) (hash-ref the-hash k #f))
                  (hash-keys the-hash))))

#;(define (dp-element-from-sol the-sym-element a-sol)
  (if (r:unsat? a-sol)
      dp-null-set
      (dp-extract-singleton (dp-set-from-sol the-sym-element a-sol))))

; recursively create a symbolic union of elements from a set, internal
; Note: At the initial call, ``k-lst'' should be ``(hash-keys H-set)''
; H-set : (hash/c any/c boolean/c) -- The underlying hash of the set to extract elements
; k-lst : (listof any/c) -- list of remaining keys of the hash to consider
(define (dp-symbolic-el H-set k-lst)
  (if (empty? k-lst)
      (error "no feasible element")
      (r:if (hash-ref H-set (car k-lst))
            (car k-lst)
            (dp-symbolic-el H-set (cdr k-lst)))))

; construct a symbolic element of a set, internal
(define (dp-symbolic-element-of a-set)
  (match-let-values
   ([(sym-S cstr-lst) (dp-symbolic-subset a-set)])
   (let* ([H (dp-set-S sym-S)]
          [first-k (car (hash-keys H))]
          [merge-func (if (dp-mergeable? first-k)
                          gen-merge-union
                          (λ (x y) x))]
          [rep-el (if (dp-mergeable? first-k)
                      (gen-representative-el-from-lst (hash-keys H) first-k)
                      #f)])
     (values (merge-func (dp-symbolic-el H (hash-keys H)) rep-el)
             cstr-lst))))

#;(define (dp-symbolic-element-of a-set)
  (let-values ([(sym-set cstrs) (dp-symbolic-subset a-set 1)])
    (values (dp-extract-singleton sym-set)
            ; Note: no need to maintain the cardinality constraint
            ;       for the set, as we are always getting the first
            ;       element in the set and the rest is ignored
            ;       in the solution the first element in the set
            ;       will be the first one satisfying the constraints
            ;       of the problem
            (append
             #;(andmap
             (λ (a-cstr-on-set)
               (λ (a-el)
                 (a-cstr-on-set sym-set)))
             cstrs)
            ; ensure some element is selected, not getting false
            (list (r:λ (a-el) a-el))))))

(define (dp-element-from-sol the-sym-element a-sol)
  (if (dp-mergeable? the-sym-element)      
      (gen-decode-merged-from-sol the-sym-element a-sol)
      (evaluate-atomic-sym the-sym-element a-sol)))

(define-syntax (element-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ ((~literal the-set-of) type-desc))
         #'type-desc]
        [(_ (~or parent-set-name:id setlike-value))
         (let*
             ([parent-set-temp-name
               (if (attribute parent-set-name)
                   #'parent-set-name
                   (generate-temporary))]
              [maybe-parsed-setlike-value
               (if
                ; matched non-id as setlike-value
                (attribute setlike-value)
                (let
                    ([parsed-part
                      (dp-expand-part #'setlike-value)])
                  (if (equal? (dp-stx-type-info-data-ref parsed-part 'el-type) 'undefined)               
                      (raise-syntax-error
                       #f
                       "not a set value"
                       #'setlike-value)
                      parsed-part))
                #f)]
              [parsed
               (if maybe-parsed-setlike-value
                   (parsed-table-with-temp-field
                    parent-set-temp-name
                    maybe-parsed-setlike-value)
                   (dp-parse-table))]
              [parent-set-entry (free-id-table-ref parsed parent-set-temp-name #f)]
              [parent-set-type
               (if parent-set-entry
                   (parsed-entry-type parent-set-entry)
                   (raise-syntax-error
                    #f
                    "undefined set"
                    #'parent-set-name))]
              [parsed-el-type
               (let ([parent-el-type (dp-stx-type-info-data-ref
                                     parent-set-type
                                     'el-type)])
                 (if (equal? parent-el-type 'undefined)
                     ; a set-like must have ''element type'' in type-info
                     (raise-syntax-error
                      #f
                      "not a valid set"
                      parent-set-temp-name)
                     parent-el-type
                     ; no longer require atomicity
                     #;(if
                      (and
                       (not (dp-stx-info-field parent-el-type atomic?))
                       (dp-part-cert-env?))
                      (raise-syntax-error
                       #f
                       "codomain must be a set of atomic elements when declared in certificate"
                       (if (attribute parent-set-name)
                           #'parent-set-name
                           #'setlike-value))
                      parent-el-type)))]
              [upstream (if maybe-parsed-setlike-value
                            (dp-stx-type-info maybe-parsed-setlike-value)
                            #'parent-set-name)]
              [upstream-accessor (dp-stx-type-info-accessor-ref parent-set-type 'set)]
              [ctc (dp-stx-info-field parsed-el-type ctc)]
              [v-dep-ctc #`(λ (a-inst)
                             (λ (a-el)
                               (and
                                (#,(dp-stx-info-field parsed-el-type v-dep-ctc) a-el)
                                (set-∈ a-el (#,upstream-accessor
                                             #,(trace-upstream-to-field upstream #'a-inst))))))]
              ; ids referred by superset or setlike-value
              [upstream-ids (append
                             (if (attribute parent-set-name) (list #'parent-set-name) '())
                             (dp-stx-type-info-field parent-set-type referred-ids '()))])
           (dp-stx-type-desc
            (generate-temporary #'element-of)
            type 'element
            kv-type-object #`#,(dp-stx-info-field parsed-el-type kv-type-object)
            atomic? #t
            upstream upstream
            upstream-accessor upstream-accessor
            ctc ctc
            v-dep-ctc v-dep-ctc
            ; (if remembered correctly) type-data are properties particular to certain types
            type-data (dp-stx-info-field parsed-el-type type-data)
            accessors (dp-stx-info-field parsed-el-type accessors)
            ; TODO: define a generator for element-of
            generator #`(λ (a-inst)
                          (λ () #t))
            ; procedure to create symbolic certificate from the object
            symbolic-constructor #`(λ (a-inst)
                                     (λ ()
                                       (dp-symbolic-element-of
                                        (#,upstream-accessor
                                          #,(trace-upstream-to-field upstream #'a-inst)))
                                       ))
            ; procedure decoding the certificate from solution object of the solver
            solution-decoder #'dp-element-from-sol
            ; null object for no solution
            null-object #'dp-null-set
            referred-ids upstream-ids))])      
      (raise-syntax-error #f unsupport-outside-problem-definition-msg stx)))





; function from instance part to, say cost of the elements in a set

;
;-----------------------
;
;  verifier utilities
;
;-----------------------



(provide

 dp-equal?  ; with wrapping of integers
 ; abbrevation of (not (equal ))
 different?
 
 ∀
 at-most-1-element-of
 ∃
 exactly-1-element-of

 sum
 max
 min
 count)

(define (dp-equal? x y)
  (r:equal? (dp-wrap-if-raw-int x) (dp-wrap-if-raw-int y)))

(define (different? x y)
  (r:not (r:equal? (dp-wrap-if-raw-int x) (dp-wrap-if-raw-int y))))



;
; Quantifiers
; Note: for x-in-X:element-of-a-set, we know that x-in-X.x is always concrete
;

(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ x-in-X:element-of-a-set expr)
     #'(r:andmap
        (r:λ (x-in-X.x)
          (r:=>
           (set-∈ x-in-X.x x-in-X.X)
           expr))
        (dp-ground-set->list x-in-X.X))]
    [(_ x-y-in-X-Y:element-of-product-of-2-sets x1-x2-expr)
     #'(r:andmap
        (r:λ (x-y-in-X-Y.x)
             (r:=>
              (set-∈ x-y-in-X-Y.x x-y-in-X-Y.X)
              (r:andmap
               (r:λ (x-y-in-X-Y.y)
                    (r:=>
                     (r:and
                      (set-∈ x-y-in-X-Y.y x-y-in-X-Y.Y)
                      x-y-in-X-Y.x-y-pred?)
                     x1-x2-expr))
               (dp-ground-set->list x-y-in-X-Y.Y))))
        (dp-ground-set->list x-y-in-X-Y.X))]))

(define-syntax (∃ stx)
  (syntax-parse stx
    [(_ x-in-X:element-of-a-set expr)
     #'(r:ormap
        (r:λ (x-in-X.x)
             (r:and
              (set-∈ x-in-X.x x-in-X.X)
              expr))
        (dp-ground-set->list x-in-X.X))]
    [(_ x-y-in-X-Y:element-of-product-of-2-sets x1-x2-expr)
     #'(r:ormap
        (r:λ (x-y-in-X-Y.x)
             (r:=>
              (set-∈ x-y-in-X-Y.x x-y-in-X-Y.X)
              (r:ormap
               (r:λ (x-y-in-X-Y.y)
                    (r:=>
                     (r:and
                      (set-∈ x-y-in-X-Y.y x-y-in-X-Y.Y)
                      x-y-in-X-Y.x-y-pred?)
                     x1-x2-expr))
               (dp-ground-set->list x-y-in-X-Y.Y))))
        (dp-ground-set->list x-y-in-X-Y.X))]))

(define-syntax (at-most-1-element-of stx)
  (syntax-parse stx
    [(_ x-in-X:element-of-a-set expr)
     #'(r:<=
        (r:count
         r:identity
         (r:map
          (r:λ (x-in-X.x)
               (r:and
                (set-∈ x-in-X.x x-in-X.X)
                expr))
          (dp-ground-set->list x-in-X.X)))
        1)]))

(define-syntax (exactly-1-element-of stx)
  (syntax-parse stx
    [(_ x-in-X:element-of-a-set expr)
     #'(r:=
        (r:count
         r:identity
         (r:map
          (r:λ (x-in-X.x)
               (r:and
                (set-∈ x-in-X.x x-in-X.X)
                expr))
          (dp-ground-set->list x-in-X.X)))
        1)]))

(define-syntax (sum stx)
  (syntax-parse stx
    [(_ val-x (~datum for) x-in-X:element-of-a-set (~optional (~seq (~datum if) pred-x?)))
     #`(r:let ([vals
                 (r:map
                  (r:λ (x-in-X.x)
                       (r:let ([is-in-set
                                 (r:and
                                  (set-∈ x-in-X.x x-in-X.X)
                                  #,(if (attribute pred-x?)
                                        #'pred-x?
                                        #t))])
                              ; keep symbolic union inside struct dp-integer
                              (let ([wrapped-val-x (dp-wrap-if-raw-int val-x)])
                                  (dp-integer (r:if is-in-set (dp-integer-val wrapped-val-x) 0)
                                          (r:if is-in-set (dp-integer-size wrapped-val-x) 'const)))))
                  (dp-ground-set->list x-in-X.X))])        
               (dp-integer
                (r:apply r:+ (r:map dp-int-unwrap vals))
                (dp-int-lst-max-size vals)))
]))

(define-syntax (max stx)
  (syntax-parse stx
    [(_ val-x (~datum for) x-in-X:element-of-a-set (~optional (~seq (~datum if) pred-x?)))
     #`(r:let ([vals
                 (r:map
                  (r:λ (x-in-X.x)
                       (r:let ([is-in-set
                                 (r:and
                                  (set-∈ x-in-X.x x-in-X.X)
                                  #,(if (attribute pred-x?)
                                        #'pred-x?
                                        #t))])
                              ; keep symbolic union inside struct dp-integer
                              (let ([wrapped-val-x (dp-wrap-if-raw-int val-x)])
                                  (dp-integer (r:if is-in-set (dp-integer-val wrapped-val-x) 0)
                                          (r:if is-in-set (dp-integer-size wrapped-val-x) 'const)))))
                  (dp-ground-set->list x-in-X.X))])        
               (dp-integer
                (r:apply r:max (r:map dp-int-unwrap vals))
                (dp-int-lst-max-size vals)))]
    [(_ v ...) #'(dp-int-max v ...)]))

(define-syntax (min stx)
  (syntax-parse stx
    [(_ val-x (~datum for) x-in-X:element-of-a-set (~optional (~seq (~datum if) pred-x?)))
     #`(r:let ([vals
                 (r:map
                  (r:λ (x-in-X.x)
                       (r:let ([is-in-set
                                 (r:and
                                  (set-∈ x-in-X.x x-in-X.X)
                                  #,(if (attribute pred-x?)
                                        #'pred-x?
                                        #t))])
                              ; keep symbolic union inside struct dp-integer
                              (let ([wrapped-val-x (dp-wrap-if-raw-int val-x)])
                                  (dp-integer (r:if is-in-set (dp-integer-val wrapped-val-x) 0)
                                          (r:if is-in-set (dp-integer-size wrapped-val-x) 'const)))))
                  (dp-ground-set->list x-in-X.X))])        
               (dp-integer
                (r:apply r:min (r:map dp-int-unwrap vals))
                (dp-int-lst-max-size vals)))]
    [(_ v ...) #'(dp-int-min v ...)]))

(define-syntax (count stx)
  (syntax-parse stx
    [(_ x-in-X:element-of-a-set (~datum s.t.) pred-x?)
     ; XXX: unfortunately we can not tell if the result is constant or poly
     ;      unless we have information from X
     #'(sum (dp-integer 1 'poly) for x-in-X if pred-x?)]))
