#lang racket

(require
  (prefix-in r: rosette)
  racket/random

  "../private/problem-definition-core.rkt"
  [for-syntax racket/list
              racket/struct
              racket/syntax
              syntax/parse
              syntax/id-table
              racket/match]
  [for-meta 2 racket/base
              syntax/parse])

(provide
 identity
 ;(struct-out neg)
 (struct-out dp-literal)
 (struct-out dp-cnf-clause)
 (struct-out dp-cnf)

 clause
 create-cnf
 
 var/c
 literal/c
 clause/c
 cnf/c
 literal
 neg
 underlying-var
 positive-literal?
 negative-literal?
 literal-neg-of?
 same-variable?
 true-literal?
 vars-of
 literals-of ; only for reduction
 literals-of-cnf
 literals-of-clause
 clauses-of
 n-true-literals
 generate-sat-instance

 ;non-solvable
 literals-with-clause-index-of

 cnf
 variables-of)

; type objects representing CNF, clauses and literals
(begin-for-syntax
  (provide tCNF
           tClause
           tLiteral)

  (struct ty-CNF ()
    #:property prop:type-interface (list (cons 'set (λ (x) (tSetOf (tClause)))))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'CNF)
        (λ (self) '())))])

  (struct ty-Clause ()
    #:property prop:type-interface (list (cons 'set (λ (x) (tSetOf (tLiteral)))))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Clause)
        (λ (self) '())))])

  (struct ty-Literal ()
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Literal)
        (λ (self) '())))])
  
  (define-match-expander tCNF
    (syntax-parser
      [(_) #'(ty-CNF)])
    (syntax-parser
      [(_) #'(ty-CNF)]))

  (define-match-expander tClause
    (syntax-parser
      [(_) #'(ty-Clause)])
    (syntax-parser
      [(_) #'(ty-Clause)]))

  (define-match-expander tLiteral
    (syntax-parser
      [(_) #'(ty-Literal)])
    (syntax-parser
      [(_) #'(ty-Literal)]))
)



(define var/c symbol?)

; fallback to Racket
; see also: dp-set
(struct dp-literal (x neg?) #:transparent
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-literal port mode)
                 (r:if (dp-literal-neg? the-literal)
                       (fprintf port "(¬'~a)" (dp-literal-x the-literal))
                       (fprintf port "'~a" (dp-literal-x the-literal)))))])

(define (literal x)
  (dp-literal x #f))
(define (neg l-or-x)
  (r:if (dp-literal? l-or-x)
        (dp-literal (dp-literal-x l-or-x) (not (dp-literal-neg? l-or-x)))
        (dp-literal l-or-x #t)))

; deprecated
(define (literal-equal? l1 l2)
  (and (equal? (dp-literal-x l1) (dp-literal-x l2))
       (equal? (dp-literal-neg? l1) (dp-literal-neg? l2))))

; test if two clauses are equivalent
; Note: casting to set from clause ensures same ground set
;       same set of literal with different ground set may not test equal
; internal (for instance generation), not mature implementation
; assuming c1 and c2 has the same arity
; deprecated
(define (clause-equal? c1 c2)
  (andmap (λ (l1)
            (ormap
             (λ (l2) (literal-equal? l1 l2))
             (dp-set-members->list c2)))
          (dp-set-members->list c1)))

;(r:struct neg (x) #:transparent)

(define literal/c
  (struct/c dp-literal var/c boolean?))

;(define literal/c (or/c var/c (struct/c neg var/c)))
; Note: currently the order of variables counts when comparing equality 
; fallback to Racket
; see also: dp-set
(struct dp-cnf-clause (lst) #:transparent
          #:property prop:interface
                    (r:list
                       (r:cons 'set (r:λ (c)
                                         (dp-list->set
                                          (dp-cnf-clause-lst c)))))
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-clause port mode)
                 (fprintf port "~a" (string-join (map
                                                  (λ (l) (format "~a" l))
                                                  (dp-cnf-clause-lst the-clause)) " ∨ "))))])
 
(define clause/c
  (struct/c dp-cnf-clause (listof literal/c)))

#;(define clause/c
    (listof literal/c))

; Note the order of clauses counts when comparing equality at this time
(r:struct dp-cnf (lst) #:transparent
          #:property prop:interface
                     (r:list
                        (r:cons 'set (r:λ (c)
                                          (dp-list->set
                                           (dp-cnf-lst c)))))
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-cnf port mode)
                 (fprintf port "[cnf\n~a\n]" (string-join (map
                                                  (λ (c) (format " (~a)" c))
                                                  (dp-cnf-lst the-cnf)) "\n"))))])
(define cnf/c
  (struct/c dp-cnf (listof clause/c)))

(define/contract (create-cnf a-set-of-clause)
  (-> (dp-setof/c clause/c) cnf/c)
  (dp-cnf (dp-set-members->list a-set-of-clause)))

#;(define cnf/c (listof clause/c))

(define (underlying-var a-literal)
  (dp-literal-x a-literal))
(kv-func-type-annotate underlying-var ((tLiteral) (tSymbol)) "a literal")

(define (positive-literal? a-literal)
  (r:not (dp-literal-neg? a-literal)))
(kv-func-type-annotate positive-literal? ((tLiteral) (tBool)) "a literal")

(define (negative-literal? a-literal)
  (dp-literal-neg? a-literal))
(kv-func-type-annotate negative-literal? ((tLiteral) (tBool)) "a literal")

(define (literal-neg-of? l1 l2)
  (r:and (same-variable? l1 l2)
         (r:xor (dp-literal-neg? l1) (dp-literal-neg? l2))))
(kv-func-type-annotate literal-neg-of? ((tLiteral) (tLiteral) (tBool)) "two literal")

#;(define (underlying-var a-literal)
  (cond [(var/c a-literal) a-literal]
        [else (neg-x a-literal)]))

(define (same-variable? literal-1 literal-2)
  (r:equal? (underlying-var literal-1) (underlying-var literal-2)))
(kv-func-type-annotate same-variable? ((tLiteral) (tLiteral) (tBool)) "two literal")

; variables that are not found in the assignment are set to false by default
; probably deprecated (assignments are mapping now)
(define (true-literal? a-literal assignment)
  (r:xor (r:hash-ref assignment (underlying-var a-literal) #f)
         (dp-literal-neg? a-literal)))

(define (n-true-literals a-clause assignment)
  (r:count
   r:identity
   (r:map
    (r:λ (l) (true-literal? l assignment))
    (dp-cnf-clause-lst a-clause))))

#;(define (n-true-literals a-clause assignment)
  (r:count
   r:identity
   (r:map
    (r:λ (l) (true-literal? l assignment))
    (clause-lst a-clause))))

#;(define (n-true-literals assignment a-clause)
  (r:count
   r:identity
   (r:map
    (r:λ (l)
         (r:if (var/c l)
              (r:hash-ref assignment l)
              (r:not (r:hash-ref assignment (neg-x l)))))
    a-clause)))

(define (clauses-of a-cnf)
  a-cnf)
(kv-func-type-annotate clauses-of ((tCNF) (tSetOf (tClause))) "a CNF")



(provide literals-of-typed-rewriter)

(define-syntax literals-of-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ (_ (tCNF)))
       (syntax-parser
         [(_ a-cnf)
          (cons #'(literals-of-cnf a-cnf) (tSetOf (tLiteral)))])]
      [(args-τ (_ (tClause)))
       (syntax-parser
         [(_ a-clause)
          (cons #'(literals-of-clause a-clause) (tSetOf (tLiteral)))])]
      [_ (syntax-parser
           [(func arg ...)
            (raise-syntax-error #f
                                (format "expect one clause or CNF, gets ~a"
                                        (map cdr type-lst))
                                #'(func arg ...) #'(arg ...))])])))
(define (literals-of-clause a-clause)
  (as-set a-clause))
(define (literals-of-cnf a-cnf)
  (dp-list->set
   (r:apply
    r:append
    (r:map
     (r:λ (c)
          (dp-cnf-clause-lst c))
     (dp-cnf-lst a-cnf)))))

; for reduction only
; the type system will choose now in the verifier
(define (literals-of a-sth)
  (r:cond [(dp-cnf-clause? a-sth) (as-set a-sth)]
          [(dp-cnf? a-sth) (dp-list->set
                            (r:apply
                             r:append
                             (r:map
                              (r:λ (c)
                                   (dp-cnf-clause-lst c))
                              (dp-cnf-lst a-sth))))]
          [r:else (r:error "does not have literals" a-sth)]))

; non-solvable(!)
; XXX: restructure cnf.rkt and base.rkt to avoid copying
(define (literals-with-clause-index-of a-cnf)
  (if (dp-cnf? a-cnf)
        (let ([mem-list (dp-set-members->list a-cnf)])
          (dp-list->set
           (apply
            append
            (map
             (λ (i)
               (map
                (λ (lit)
                  ; index of set and subscripts of elements start from 1
                  (cons lit (+ i 1)))
                (dp-cnf-clause-lst (list-ref mem-list i))))
             (range (length mem-list))))))
        (error "not a cnf" a-cnf)))

#;(define (literals-of a-sth)
  (cond [(clause/c a-sth) (clause-lst a-sth)]
        [(cnf/c a-sth) (r:flatten a-sth)]))

; get all variables of a cnf or clause as a list
; a-sth: (or/c clause? dp-cnf?)
; -> (listof var/c[?])
; internal
(define (vars-of-list a-sth)
   (r:cond [(dp-cnf-clause? a-sth)
            (r:remove-duplicates
             (r:map underlying-var (dp-cnf-clause-lst a-sth)))]
           [(dp-cnf? a-sth)
            (r:remove-duplicates (r:flatten (r:map vars-of-list (dp-cnf-lst a-sth))))])
)

; get all variables of a cnf or clause as a set
; a-sth: (or/c clause? dp-cnf?)
; -> (dp-set-of var/c[?])
(define (vars-of a-sth)
  (dp-list->set (vars-of-list a-sth)))

#;(define (vars-of a-sth)
  (r:cond [(clause/c a-sth)
         (r:remove-duplicates
          (r:map underlying-var (clause-lst a-sth)))]
        [(cnf/c a-sth)
         (r:remove-duplicates (r:flatten (r:map vars-of a-sth)))])
  )

; compile-time functions to support cnf literal parsing
(begin-for-syntax

  ; Question: why this does not work
  #;(define-syntax-class lit
    #:datum-literals (¬)
    (pattern (~or* ((~seq (~and ¬ neg)) x) (x))))
  #;(define (parse-clause stx i)
    (syntax-parse stx
      #:datum-literals (∨)
      [(literal0:lit (~seq ∨ literal1:lit) ...)
       #`(clause (list (literal literal0.x #,(if (attribute literal0.neg) #t #f) #,i)
                       (literal literal1.x #,(if (attribute literal1.neg) #t #f) #,i)
                       ...))]))

  (define (parse-literal stx)
    (syntax-parse stx
      #:datum-literals (¬)
      [(¬ x) #`(dp-literal x #t)]
      [(x) #`(dp-literal x #f)]
      [x #`(dp-literal x #f)]))
  
  (define (parse-clause stx)
    (syntax-parse stx
      #:datum-literals (∨)
      [(literal0 (~seq ∨ literal1) ...)
       (let ([literals (map (λ (l-stx) (parse-literal l-stx))
                            (syntax->list #'(literal0 literal1 ...)))])
       #`(dp-cnf-clause (list #,@literals)))]))
)

(define-syntax (clause stx)
  (syntax-parse stx
    [(_ clause-content)
     (parse-clause #'clause-content)]))


(define (generate-sat-instance
                  n-clauses n-vars
                  #:exact-n? [e-n? #f]
                  #:arity [arity #f])
  ; not very meaningful to have no contract here
  ;(-> integer? integer? sat-instance/c)
  
  (define (generate-clause n-vars i-clause)

    (define (draw-k-var n-vars k)
        (map (λ (x) (string->symbol
                   (string-append "x" (number->string x))))
             (random-sample
              (stream->list (in-range 1 (+ n-vars 1)))
              k
              #:replacement? #f)))

    (define (generate-literal-from-var var)
      (dp-literal var (random-ref '(#t #f))))

    ; XXX: magic number
    (dp-cnf-clause (map generate-literal-from-var (draw-k-var n-vars (if arity
                                                                         arity
                                                                         (random 2 5))))))
 
  (define (generate-sat-instance-aux i n-vars res-sat-instance)
       (cond [(eq? i n-clauses) res-sat-instance]
             [else (let* ([a-clause (generate-clause n-vars i)]
                          [repeated?
                           (member a-clause res-sat-instance
                                   (λ (x y) (clause-equal? x y)))]
                          [draw-another? (and e-n? repeated?)])
                    (generate-sat-instance-aux
                    (if draw-another? i (+ i 1))
                    n-vars
                    (if repeated?
                        res-sat-instance
                        (cons
                          a-clause
                          res-sat-instance))))]))
  
  (dp-cnf (generate-sat-instance-aux 0 n-vars '())))

#;(define (generate-sat-instance
                  n-clauses n-vars
                  #:exact-n? [e-n? #f])
  ; not very meaningful to have no contract here
  ;(-> integer? integer? sat-instance/c)
  
  (define (generate-clause n-vars i-clause)

    (define (draw-3-var n-vars)
        (map (λ (x) (string->symbol
                   (string-append "x" (number->string x))))
             (random-sample
              (stream->list (in-range 1 (+ n-vars 1)))
              3
              #:replacement? #f)))

    (define (generate-literal-from-var var i-clause)
      (literal var (random-ref '(#t #f)) i-clause))

    (clause (map generate-literal-from-var (draw-3-var n-vars) (make-list 3 i-clause))))
 
  (define (generate-sat-instance-aux i n-vars res-sat-instance)
       (cond [(eq? i n-clauses) res-sat-instance]
             [else (let* ([a-clause (generate-clause n-vars i)]
                          [repeated?
                           (member a-clause res-sat-instance
                                   (λ (x y) (andmap literal-equal? x y)))]
                          [draw-another? (and e-n? repeated?)])
                    (generate-sat-instance-aux
                    (if draw-another? i (+ i 1))
                    n-vars
                    (if repeated?
                        res-sat-instance
                        (cons
                          a-clause
                          res-sat-instance))))]))
  
  (generate-sat-instance-aux 0 n-vars '()))


#;(define (generate-sat-instance
                  n-clauses n-vars
                  #:exact-n? [e-n? #f])
  ; not very meaningful to have no contract here
  ;(-> integer? integer? sat-instance/c)
  
  (define (generate-clause n-vars)

    (define (draw-3-var n-vars)
        (map (λ (x) (string->symbol
                   (string-append "x" (number->string x))))
             (random-sample
              (stream->list (in-range 1 (+ n-vars 1)))
              3
              #:replacement? #f)))

    (define (generate-literal-from-var var)
        (if (random-ref '(#t #f))
            var
            (neg var)))

    (map generate-literal-from-var (draw-3-var n-vars)))
 
  (define (generate-sat-instance-aux i n-vars res-sat-instance)
       (cond [(eq? i n-clauses) res-sat-instance]
             [else (let* ([a-clause (generate-clause n-vars)]
                          [repeated? (member a-clause res-sat-instance)]
                          [draw-another? (and e-n? repeated?)])
                    (generate-sat-instance-aux
                    (if draw-another? i (+ i 1))
                    n-vars
                    (if repeated?
                        res-sat-instance
                        (cons
                          a-clause
                          res-sat-instance))))]))
  
  (generate-sat-instance-aux 0 n-vars '()))


; parsing in problem definition

(define-syntax (cnf stx)
    (if (dp-parse-table)
      (if (not (dp-part-cert-env?))
          (syntax-parse stx
            [(_ (~optional (~seq #:arity arity:nat)))
             (let* ([maybe-arity (if (attribute arity) (syntax-e #'arity) #f)]
                    [el-ctc (if maybe-arity
                                ; XXX: use clause/c or simply dp-set/c?
                                #`(λ (a-clause)
                                   (and (clause/c a-clause)
                                        ; maybe better changing to =/c, see also ```set''' in dp-core
                                        (equal? (set-size a-clause) #,maybe-arity)))
                                #'clause/c)]
                    [el-v-dep-ctc #'v-dep-any/c]
                    ; XXX: check cnf/c or dp-setof/c?
                    [ctc #`(dp-setof/c #,el-ctc)]
                    [v-dep-ctc #'v-dep-any/c])
               (dp-stx-type-desc
                (generate-temporary 'cnf)
                type 'cnf
                kv-type-object #'(tCNF)
                atomic? #f
                el-type (dp-stx-info
                          type 'clause
                          atomic? #f
                          ctc el-ctc
                          v-dep-ctc el-v-dep-ctc
                          arity maybe-arity)
                ctc ctc
                v-dep-ctc v-dep-ctc
                type-data (list (cons 'var-type
                                      (dp-stx-info
                                       type 'boolean-variable
                                       kv-type-object #'(tSymbol)
                                       atomic? #t
                                       ctc #'var/c
                                       v-dep-ctc #'v-dep-any/c
                                       type-data '()
                                       accessors '())))
                accessors (list (cons 'set #'identity)
                                (cons 'variables #'vars-of))
                generator #`(λ (a-inst)
                              (λ ()
                                ; XXX: magic number
                                (generate-sat-instance 15 3 #:arity #,maybe-arity)))))])
          (raise-syntax-error #f "can not be used in certificate" stx))
      (syntax-parse stx
        ; TODO: add support for ∧ seperator
        ;#:datum-literals (∧)
        [(_ clause0 ...)
         #:with (parsed-clause0 ...)
                (let ([clauses (syntax->list #'(clause0 ...))])
                  (map (λ (i) (parse-clause (list-ref clauses i)))
                       (range (length clauses))))
         #'(dp-cnf (list parsed-clause0 ...))])))

(define-syntax (variables-of stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ parent-name:id)
         (let*
             ([the-parent (get-field-from-parsed #'parent-name)]
              [var-type-desc (dp-stx-type-info-data-ref the-parent 'var-type)]
              [upstream-accessor
               (if (equal? var-type-desc 'undefined)
                   (raise-syntax-error #f "object does not have variables" #'parent-name)
                   (dp-stx-type-info-accessor-ref the-parent 'variables))]
              [upstream-ids (cons
                             #'parent-name
                             (dp-stx-type-info-field the-parent referred-ids '()))])
           (dp-stx-type-info
            (generate-temporary #'variables-of)
            type 'set
            kv-type-object #'(tSetOf (tSymbol))
            atomic? #f
            ctc #`(dp-setof/c #,(dp-stx-info-field var-type-desc ctc))
            v-dep-ctc #`(dp-setof-d/c #,(dp-stx-info-field var-type-desc v-dep-ctc))    
            upstream #'parent-name
            upstream-accessor upstream-accessor
            type-data (list (cons 'el-type var-type-desc))
            accessors (list (cons 'set #'identity))
            referred-ids upstream-ids))])
      (syntax-parse stx
        [(_ x)
         #'(vars-of x)])))

(kv-func-type-annotate variables-of ((or (tCNF) (tClause)) (tSetOf (tSymbol)))
                       "a CNF or a clause")
