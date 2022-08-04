#lang racket

(require "problem-definition-utility.rkt"
         "verifier-type.rkt"
         "primitive-data-type.rkt"
         "core-structures.rkt"
         "karp-contract.rkt"
         racket/stxparam
         [for-syntax racket/pretty
                     racket/require
                     racket/list
                     racket/match
                     racket/syntax
                     racket/function
                     syntax/parse
                     syntax/id-table
                     syntax/stx
                     racket/syntax-srcloc]
         [prefix-in r: rosette/safe])

; type info
(require "dp-type-info.rkt")
(provide (rename-out [dp-define define]))

(provide decision-problem
         is-a
         yes-instance/kc
         yes-instance/c
         no-instance/kc
         no-instance/c)


; problem formulation
(define (yes-instance/kc
         instance/kc
         problem-solver
         empty-certificiate)
  (and/kc instance/kc
          (make-simple-contract/kc (p)
            (not (dp-equal? empty-certificiate
                            (problem-solver p)))
            "expects a yes instance")))
(define (yes-instance/c
         instance/c
         problem-solver
         empty-certificiate)
  (and/c instance/c
         (λ (p)
           (not (equal? empty-certificiate
                 (problem-solver p))))))

(define (no-instance/kc
         instance/kc
         problem-solver
         empty-certificiate)
  (and/kc instance/kc
          (make-simple-contract/kc (p)
            (dp-equal? empty-certificiate
                       (problem-solver p))
            "expects a no instance")))
(define (no-instance/c
         instance/c
         problem-solver
         empty-certificiate)
  (and/c instance/c
         (λ (p)
           (equal? empty-certificiate
                 (problem-solver p)))))

(define-syntax is-a
  (λ _
    (raise-syntax-error 'is-a "is-a can only be used in problem definition")))

(begin-for-syntax

  (define-syntax-class field-desc
    #:literals (is-a)
    (pattern [field-id:id is-a field-type]))

  ; substitute all presence of any key of ```id-tbl''' in ```stx''' with corresponding value
  ; --> syntax?
  (define (stx-subst-with-id-table stx id-tbl)
    (if (equal? (free-id-table-count id-tbl) 0) ; slight optimization,
        stx                                     ; skip if nothing to substitute
        (syntax-parse stx
          [x:id (let ([new (free-id-table-ref id-tbl #'x #f)])
                  (if new new #'x))]
          [(x) #:with res (stx-subst-with-id-table #'x id-tbl)
               #'(res)]
          [(x y ...+) #:with res-first (stx-subst-with-id-table #'x id-tbl)
                      #:with res-rest (stx-subst-with-id-table #'(y ...) id-tbl)
                      (syntax-parse #'(res-first res-rest) ;syntax-cons(?)
                        [(z (w ...)) #'(z w ...)])
                      ]
          [anything-else #'anything-else])))
  
  ; returns the parsing table with instance entries
  ; --> (cons parsed-result instance-field-lst)
  ; parsed-result      : free-id-table from field id to (cons field-type-info field-index)
  ; instance-field-lst : the list of field id,
  ;                      order of items given by the problem definition
  ; Note: the field-index is used in ``trace-upstream-to-field'' in parsing subsequent fields
  (define (dp-parse-instance parsed rest)
    (syntax-parse rest
      #:literals (is-a)
      [() (cons parsed '())]
      [(cur-part:field-desc leftover ...)
       (let* ([new-entry
               (if (free-id-table-ref parsed #'cur-part.field-id #f)
                   (raise-syntax-error (syntax->datum #'cur-part.field-id)
                                       "already defined" #'cur-part)
                   (parameterize ([dp-parse-table parsed]
                                  [dp-cur-field-id #'cur-part.field-id])
                     (dp-stx-type-info
                      #'cur-part.field-id
                      (dp-stx-type-desc
                       (dp-expand-part
                        #'cur-part.field-type))
                      )))]
              [updated-parsed (free-id-table-set
                               parsed
                               #'cur-part.field-id
                               ; Concate the index (order in the instance) of this field 
                               ; along with instance field type information.
                               ; This is to provide position of the fields in the acutal value
                               ; to macros that have only access to dp-parse-table besides local info
                               (cons new-entry (free-id-table-count parsed)))])
         ; let body
         (match-let
             ([(cons next-parsed parsed-lst) (dp-parse-instance updated-parsed #'(leftover ...))])
           (cons next-parsed (cons #'cur-part.field-id parsed-lst))))]))

    ; helper function to drop the indices in free-id-table
    (define (free-id-table-map-value proc table)
      (define (map-aux table keys proc)
        (cond [(empty? keys) table]
              [else (map-aux (free-id-table-set
                              table
                              (car keys)
                              (proc (free-id-table-ref table (car keys))))
                             (cdr keys)
                             proc)]))
      
      (map-aux table (free-id-table-keys table) proc))

    ; get the element struct info to create and substitution table for contracts from parsed table
    ; --> (cons el-type-to-make-list subst-tbl)
    ; el-type-to-make-list : (listof (hash/c symbol? (?)))
    ; subst-tbl : free-id-table? -- from ctc placeholder ids to syntax objects of ctcs
    (define (collect-el-type-to-make-from-table table ctx)
      (define (collect-aux table keys)
        (cond [(empty? keys) (cons '() (make-immutable-free-id-table))]
              [else (let ([field-value
                           (dp-stx-type-info-field (free-id-table-ref table (car keys)) el-type-to-make)]
                          [rest (collect-aux table (cdr keys))])
                      (if (equal? field-value 'undefined)
                          rest ; no new element type to create
                          (let ([type-name-with-ctx
                                 (format-id ctx "~a" (hash-ref field-value 'type-name))])
                            (cons
                             (cons
                              (hash-set
                               field-value 'type-name type-name-with-ctx)
                              (car rest))
                             (free-id-table-set
                              (cdr rest)
                              (hash-ref field-value 'placeholder)
                              #`(struct/c #,type-name-with-ctx
                                          any/c
                                          #,@(map
                                             ; XXX: all attributes are restricted to integers now
                                             (λ (x) #'integer?)
                                             (hash-ref field-value 'attrs))))))))]))
      
      (collect-aux table (free-id-table-keys table)))

    ;
    ;-------------------------------------
    ;
    ;   Verifier Type System
    ;
    ;-------------------------------------
    ;

    ; type object of the field accessors
    ; Question: does ``#:transparent'' matters?
    (struct tAccessor (ty-field) #:transparent)

    ; cert-pair : (cons/c stx/c τb/c)
    ; inst-field-pair-lst : (listof (cons/c stx/c τb/c))
    (define (dp-verifier-rewrite kv-stxs cert-pair inst-field-pair-lst)
      ;(pretty-print kv-stxs) -- for debugging
      (define (dp-verifier-rw-aux kv-stxs env)
        (syntax-parse kv-stxs
          [(last-expr)
           ; make the result a syntax of a list, to work with the splicing at a)
           (let ([rw-pair (dp-typecheck-rewrite #'last-expr env)])
             (match (cdr (get-τb rw-pair))
               [(tBool) #`(#,(car rw-pair))]
               [_ (raise-syntax-error #f "verifier expects a boolean expression" kv-stxs)]))
           #;#`(#,(car (dp-typecheck-rewrite #'last-expr env)))]
          [(cur-part leftover ...+)
           (syntax-parse #'cur-part
             ; use datum-literals as the ``define'' at this scope is not
             ; free-identifier=? to the ``define'' in the verifier
             #:datum-literals (define)
             [(define x:id kv-expr:expr)
              (let* ([rw-pair (dp-typecheck-rewrite #'kv-expr env)]
                     [cur-part #`(define x #,(car rw-pair))]
                     ; (Maybe) TODO: add check if ``x'' is already in the env
                     [updated-env (free-id-table-set env #'x (cdr rw-pair))])
                ; a), 2nd position
                #`(#,cur-part #,@(dp-verifier-rw-aux #'(leftover ...) updated-env)))])
           ]))
      
      (define rw-stxs
        (dp-verifier-rw-aux
         kv-stxs
         (make-immutable-free-id-table
          (cons (cons (car cert-pair) (make-τ 'SYM (cdr cert-pair)))
                (map (λ (a-pair)
                       (cons (car a-pair) (make-τ 'CON (tAccessor (cdr a-pair)))))
                     inst-field-pair-lst)))))

      ;(pretty-print rw-stxs)
      
      rw-stxs)

    (define-syntax-class set-agg-op-bool
      #:literals (∀ ∃ at-most-1-element-of exactly-1-element-of)
      (pattern (~or ∀ ∃ at-most-1-element-of exactly-1-element-of)))

    (define-syntax-class set-agg-op-int
      #:literals (sum max min)
      (pattern (~or sum max min)))

    (define (tag-max tag-lst)
      (cond [(empty? tag-lst) 'CON]
            [else (if (equal? (car tag-lst) 'SYM)
                      'SYM
                      (tag-max (cdr tag-lst)))]))

    (define (dp-typecheck-rewrite stx env)
      (syntax-parse stx
        [x:id (let ([lookup-res (free-id-table-ref env stx #f)])
                (if (not lookup-res)
                    ; add ``kv$'' for debugging (for now)
                    (raise-syntax-error #f "unbound variable" #'x)
                    (cons stx lookup-res)))]
        ; put the 2 sets case here as below uses ~! to commit when matching ``agg-op''
        [(agg-op:set-agg-op-bool x-y-in-X-Y:element-of-product-of-2-sets body-expr:expr)
         (let* ([rw-pair-X (dp-typecheck-rewrite #'x-y-in-X-Y.X env)]
                [τb-el-X (match (get-τb (cdr rw-pair-X))
                           [(tSetOf ty-el) ty-el]
                           [_ (raise-syntax-error #f "expects a set" stx #'x-y-in-X-Y.X)])]
                [rw-pair-Y (dp-typecheck-rewrite #'x-y-in-X-Y.Y env)]
                [τb-el-Y (match (get-τb (cdr rw-pair-Y))
                           [(tSetOf ty-el) ty-el]
                           [_ (raise-syntax-error #f "expects a set" stx #'x-y-in-X-Y.Y)])]
                [env-x-y (free-id-table-set* env #'x-y-in-X-Y.x (make-τ 'CON τb-el-X)
                                                 #'x-y-in-X-Y.y (make-τ 'CON τb-el-Y))]               
                [rw-pair-pred?
                 (dp-typecheck-rewrite #'x-y-in-X-Y.x-y-pred? env-x-y)]
                [τb-pred?
                 (match (get-τb (cdr rw-pair-pred?))
                   [(tBool) (tBool)]
                   [_ (raise-syntax-error #f "expects a boolean expression" stx #'x-y-in-X-Y.x-y-pred?)])]
                [rw-pair-body
                 (dp-typecheck-rewrite #'body-expr env-x-y)])
           (cons #`(agg-op [(x-y-in-X-Y.x x-y-in-X-Y.y) ∈ (#,(car rw-pair-X) × #,(car rw-pair-Y))
                            where #,(car rw-pair-pred?)]
                           #,(car rw-pair-body))
                 (make-τ
                  (tag-max (list (get-tag (cdr rw-pair-X))
                                (get-tag (cdr rw-pair-Y))
                                (get-tag (cdr rw-pair-pred?))
                                (get-tag (cdr rw-pair-body))))
                  (match (get-τb (cdr rw-pair-body))
                    [(tBool) (tBool)]
                    [_ (raise-syntax-error #f "expects a boolean expression" stx #'body-expr)]))))]
        ; use ~! to commit to this branch when ``agg-op'' is matched
        ; i.e., it fails if the remaining does not match
        [(agg-op:set-agg-op-bool ~! x-in-X:element-of-a-set body-expr:expr)
         (let* ([rw-pair-X (dp-typecheck-rewrite #'x-in-X.X env)]
                [τb-el-X (match (get-τb (cdr rw-pair-X))
                           [(tSetOf ty-el) ty-el]
                           [_ (raise-syntax-error #f "expects a set" stx #'x-in-X.X)])]
                [rw-pair-body
                 (dp-typecheck-rewrite #'body-expr
                                       (free-id-table-set env #'x-in-X.x (make-τ 'CON τb-el-X)))])
           (cons #`(agg-op [x-in-X.x ∈ #,(car rw-pair-X)] #,(car rw-pair-body))
                 (make-τ
                  (tag-max (list (get-tag (cdr rw-pair-X)) (get-tag (cdr rw-pair-body))))
                  (match (get-τb (cdr rw-pair-body))
                    [(tBool) (tBool)]
                    [_ (raise-syntax-error #f "expects a boolean expression" stx #'body-expr)]))))]
        [(agg-op:set-agg-op-int ~! body-expr (~datum for) x-in-X:element-of-a-set (~optional (~seq (~datum if) pred-x?)))
         (let* ([rw-pair-X (dp-typecheck-rewrite #'x-in-X.X env)]
                [τb-el-X (match (get-τb (cdr rw-pair-X))
                           [(tSetOf ty-el) ty-el]
                           [_ (raise-syntax-error #f "can not be used as a set" stx #'x-in-X.X)])]
                [rw-pair-pred-x?
                 (if (attribute pred-x?)
                     (dp-typecheck-rewrite #'pred-x?
                                           (free-id-table-set env #'x-in-X.x (make-τ 'CON τb-el-X)))
                     #f)]
                [τb-pred-x? (if rw-pair-pred-x?
                             (match (get-τb (cdr rw-pair-pred-x?))
                              [(tBool) (tBool)]
                              [_ (raise-syntax-error #f "expects a boolean expression" stx #'pred-x?)])
                             #f)]
                [rw-pair-body
                 (dp-typecheck-rewrite #'body-expr
                                       (free-id-table-set env #'x-in-X.x (make-τ 'CON τb-el-X)))]
                [τb-body (match (get-τb (cdr rw-pair-body))
                            [(tInt) (tInt)]
                            [_ (raise-syntax-error #f "expects an integer expression" stx #'body-expr)])])
           (cons #`(agg-op #,(car rw-pair-body) for [x-in-X.x ∈ #,(car rw-pair-X)]
                           #,@(if (attribute pred-x?) #`(if #,(car rw-pair-pred-x?)) #'()))
                 (make-τ
                  (tag-max (list (get-tag (cdr rw-pair-X))
                                 (get-tag (cdr rw-pair-body))
                                 (if rw-pair-pred-x? (get-tag (cdr rw-pair-pred-x?)) 'CON)))
                  (tInt))))]
        [(accessor:id inst-id) ; maybe ``inst-id:id'' (?)
         #:when (tAccessor?
                 (get-τb (free-id-table-ref env #'accessor (cons #f #f)))) ; (cons #f #f) for not found
         (cons stx
               (make-τ 'CON (tAccessor-ty-field (get-τb (free-id-table-ref env #'accessor)))))]
        [(func:id arg ...)
         #:with rewriter-id (format-id #'func "~a-typed-rewriter" #'func)
         #:attr rewriter-in-scope? (identifier-binding #'rewriter-id)
         #:fail-unless (attribute rewriter-in-scope?) "not a function" ; is the message ever used(?)
         (let* ([rw-pair-lst
                 (map (λ (a-stx)
                        (dp-typecheck-rewrite a-stx env))
                      (stx->list #'(arg ...)))]
                [rw-stx-lst (map car rw-pair-lst)]
                [arg-τ-lst (map cdr rw-pair-lst)]
                [arg-tag-lst (map get-tag arg-τ-lst)]
                ; get the corresponding rewriter from tag-type pattern of the arguments
                [func-stx-rewriter ((syntax-local-value #'rewriter-id) arg-τ-lst)]
                ; func-stx-rewriter is a syntax transformer rewriting the whole (application) expression
                ; returns (cons rw-res-stx rw-res-τb)
                [rw-res-pair (func-stx-rewriter #`(func #,@rw-stx-lst))])
           (cons (car rw-res-pair) (make-τ (tag-max arg-tag-lst) (cdr rw-res-pair))))]
        [(a-mapping key)
         #:with rewriter-id (format-id #'a-mapping "lookup-typed-rewriter")
         #:attr rewriter-in-scope? (identifier-binding #'rewriter-id)
         #:fail-unless (attribute rewriter-in-scope?) "mapping lib not requried" ; is the message ever used(?)
         (let* ([rw-pair-a-mapping (dp-typecheck-rewrite #'a-mapping env)]
                [rw-pair-key (dp-typecheck-rewrite #'key env)]
                [lookup-rewriter ((syntax-local-value #'rewriter-id)
                                  (list (cdr rw-pair-a-mapping) (cdr rw-pair-key)))]
                ; func-stx-rewriter is a syntax transformer rewriting the whole (application) expression
                ; returns (cons rw-res-stx rw-res-τb)
                [rw-res-pair (lookup-rewriter #`(#,(car rw-pair-a-mapping)
                                                 #,(car rw-pair-key)))])
           (cons (car rw-res-pair)
                 (make-τ (tag-max (list (get-tag (cdr rw-pair-a-mapping))
                                        (get-tag (cdr rw-pair-key))))
                         (cdr rw-res-pair))))
        ]
        ; literals
        [b:boolean (cons stx (make-τ 'CON (tBool)))]
        [i:integer (cons stx (make-τ 'CON (tInt)))]
        [_ (raise-syntax-error #f "invalid expression" stx)]))

    ;
    ;-------------------------------------
    ; end of Verifier Type System
  )

(define-syntax (void-if-id-presents stx)
  (syntax-parse stx
    [(_ the-id:id content)
     (if (identifier-binding #'the-id)
         #'(begin) ; what is better for null stx?
         #'content)]))

(define-syntax (decision-problem stx)
  (parameterize ([dp-parse-table #t])
    (syntax-parse stx
      [(_ (~seq #:name name:id)
          (~seq #:instance inst)
          (~seq #:certificate cert))
        #:with un#-in-template (quote-syntax unsyntax)
        #:with un#@-in-template (quote-syntax unsyntax-splicing)
       (let* ([parsed-result
              (dp-parse-instance (make-immutable-free-id-table)
                                 #'inst)]
              [parsed (free-id-table-map-value car (car parsed-result))]
              [instance-field-lst (cdr parsed-result)]
              [el-types-to-make-info (collect-el-type-to-make-from-table parsed #'name)]
              [el-types-to-make (car el-types-to-make-info)]
              [ctc-subst-tbl (cdr el-types-to-make-info)]
              [cert-parsed-type
               (parameterize ([dp-parse-table (car parsed-result)]
                              [dp-part-cert-env? #t])
                 (dp-stx-type-desc
                  (dp-expand-part
                   #'cert)))]
              [valid-cert-type (if (equal?
                                    (dp-stx-info-field cert-parsed-type symbolic-constructor)
                                    'undefined)
                                   (raise-syntax-error #f "can not be used as a certificate" #'cert)
                                   #t)])
         (with-syntax*
             ([instance (format-id #'name "~a-instance" #'name)]
              [define/instance (format-id #'name "define/~a-instance" #'name)]
              [create-instance (format-id #'name "create-~a-instance" #'name)]
              [instance-type-info (format-id #'name "dp-instance-type-~a" #'name)]
              [instance-type-annotate (format-id #'name "dp-annotate-instance-type-~a" #'name)]
              [instance/kc
               (format-id #'name "~a-instance/kc" #'name)]
              [instance/c
               (format-id #'name "~a-instance/c" #'name)]
              ;[certificate (format-id #'name "~a-certificate" #'name)]
              [certificate/kc
               (format-id #'name "~a-certificate/kc" #'name)]
              [certificate/c
               (format-id #'name "~a-certificate/c" #'name)]
              [define-verifier-id (format-id #'name "define-~a-verifier" #'name)]
              [verifier-id (format-id #'name "~a-verifier" #'name)]
              [null-cert (format-id #'name "null-~a-cert" #'name)]
              [yes/kc
               (format-id #'name "yes-~a/kc" #'name)]
              [yes/c
               (format-id #'name "yes-~a/c" #'name)]
              [no/kc
               (format-id #'name "no-~a/kc" #'name)]
              [no/c
               (format-id #'name "no-~a/c" #'name)]
              [instance-generator (format-id #'name "generate-~a-instance" #'name)]
              [inst-pretty-printer (format-id #'name "pretty-print-~a-instance" #'name)]
              [cert-pretty-printer (format-id #'name "pretty-print-~a-certificate" #'name)]
              #;[the-solver (or (attribute custom-solver) #'default-solver)])
           #`(begin

               (provide define/instance
                        create-instance
                        instance/kc
                        instance/c
                        ;certificate
                        certificate/kc
                        ;certificate/c
                        instance-generator
                        inst-pretty-printer
                        cert-pretty-printer
                        instance-type-info
                        #,@instance-field-lst)
               
               ; introducing the dummy identifiers to repair the arrows
               ; ```1''' is dummy
               (void (let (#,@(for/list ([field (free-id-table-keys parsed)])
                                #`[#,(syntax-property field 'original-for-check-syntax #t) 1]))
                       (begin
                         1 ; dummy
                         #,@(map
                             (λ (stx) (syntax-property stx 'original-for-check-syntax #t))
                             (flatten  
                              (cons
                               (dp-stx-info-field cert-parsed-type referred-ids '())
                               (for/list ([field-type (free-id-table-values parsed)])
                                 (dp-stx-type-info-field field-type referred-ids '())))
                              )))))
               ; for debugging the arrows, return the the positions of identifiers
               #;'#,(list
                     (map (λ (stx)
                            (list (syntax-e stx)
                                  (syntax-line stx)
                                  (syntax-column stx)
                                  (syntax-original? stx)))
                          (free-id-table-keys parsed))
                     (map (λ (stx)
                            (list
                             (syntax-e stx)
                             (syntax-line stx)
                             (syntax-column stx)
                             (syntax-original? stx)))
                          (flatten
                           (cons
                            (dp-stx-info-field cert-parsed-type referred-ids '())
                            (for/list ([field-type (free-id-table-values parsed)])
                              (dp-stx-type-info-field field-type referred-ids '()))
                            ))))

               ; nominal instance contract
               (define instance/kc
                 (kc-contract (v the-srcloc name context [predicate? #f])
                   (cond
                     [(not (dp-instance? v))
                      (contract-fail/kc
                       the-srcloc name
                       (format "expects ~v" 'instance)
                       context
                       v predicate?)]
                     [(not (and
                            (list? (dp-instance-fields v))
                            (symbol? (list-ref (dp-instance-fields v) 0))))
                      (error "instance fields internal error")]
                     [(not (equal? (list-ref (dp-instance-fields v) 0) 'instance))
                      (contract-fail/kc
                       the-srcloc name                       
                       (format "expects ~v (not ~e)" 'instance
                                             (list-ref (dp-instance-fields v) 0))
                       context
                       v predicate?)
                      ; TODO: should squeeze this piece of information somewhere
                      ; given (list-ref (dp-instance-fields x) 0)
                      ]
                     [else (if predicate? #t v)])))
               
               (define (instance/c x)
                 (make-flat-contract
                  #:name 'instance
                  #:first-order
                  (λ (x)
                    (and (dp-instance? x)
                         (list? (dp-instance-fields x))
                         (equal? (list-ref (dp-instance-fields x) 0) 'instance)))
                  #:late-neg-projection
                  (λ (blame)
                    (λ (x neg-party)
                      (cond [(not (dp-instance? x))
                             (raise-blame-error
                              blame
                              #:missing-party neg-party
                              x '(expected ,instance given: "~e") 
                              x)]
                            [(not (and
                                   (list? (dp-instance-fields x))
                                   (symbol? (list-ref (dp-instance-fields x) 0))))
                             (error "instance fields internal error")]
                            [(not (equal? (list-ref (dp-instance-fields x) 0) 'instance))
                             (raise-blame-error
                              blame
                              #:missing-party neg-party
                              x '(expected ,instance given: "~e") 
                              (list-ref (dp-instance-fields x) 0))]
                            [else x])))
                  ))
               ; instance object type information
               (define-syntax instance-type-info
                 (type-info 'instance ;(format-symbol "~a-instance" 'name)
                            ; field name : symbol? -> index : natural?
                            #,(for/hash ([i (range (length instance-field-lst))])
                                (values (syntax-e (list-ref instance-field-lst i)) (+ i 1)))
                            #'error))

               ; add context information of which field for the error message of a blame in creating instance
               (define (add-field-context blame field-name)
                 (blame-add-context blame (format "in the ~a field of" field-name)))

               (define (add-field-context/kc context field-name)
                 (cons (format "the ~a field" field-name) context))

               
               (begin-for-syntax
                 (define (instance-type-annotate runtime-object-id)
                   ; creates a (compile-time) value with type information of the instance
                   ; which translates to another id corresponding to the object for run time
                   ; binding a transformer id to this value creates annotation for that id           
                   (let ([the-type-info
                          (syntax-local-value #'instance-type-info)])
                     ; copy type description and change the underlying runtime id
                     (struct-copy
                      type-info
                      the-type-info
                      [#,(quote-syntax runtime-id) runtime-object-id])))
                 ; export the type annotation binding
                 (provide instance-type-annotate)

                 ; contracts for instance objects
                 ; Note: can not instead for every field generate a contract given the instance
                 ; and then check each field with the contract generated
                 ; because the validity of the previous fields that the contract of later fields
                 ; depends on are not checked when generating the contract for later fields
                 ; Therefore the design seperate the contract to flat ones and value-dependent ones
                 
                 ; contract list for instance fields, flat part
                 (define flat-ctc-lst ; indices aligned with ```field-lst'''
                   (syntax->list
                    ; can not be quasisyntax here
                    ; get here from trying '#,@(for/list ([a-field ....]) ....) first
                    ; why not #'(list #,@(for/list ....)) ?
                    #'#,(for/list ([a-field instance-field-lst])
                          (stx-subst-with-id-table
                           (dp-stx-type-info-field (free-id-table-ref parsed a-field) ctc)
                           ctc-subst-tbl))))
                 
                 ;(raise-syntax-error flat-ctc-lst #f) -- debug use, used to check what's in ctc-list

                 ; instance value dependent contracts list for instnace fields
                 (define v-dep-ctc-lst
                   (syntax->list
                    #'#,(for/list ([a-field instance-field-lst])
                          (stx-subst-with-id-table
                           (dp-stx-type-info-field (free-id-table-ref parsed a-field) v-dep-ctc)
                           ctc-subst-tbl))))

                 (define instance-fields-name (syntax->list #'#,instance-field-lst))


                 (define inst-ctc/kc
                   #`(kc-contract (a-inst the-srcloc name context [predicate? #f])
                      ; first check if a-inst is an instance
                      ; this is a sanity check, should already be enforced with the
                      ; define- and create-instances
                      (when (not (dp-instance? a-inst))
                        (error "instance contract internal error"))
                      (define the-field-names (syntax->datum #'#,instance-fields-name))
                      ; result is only used when predicate? is #t
                      (define flat-result
                        (for/and
                          ([i (range (length the-field-names))]
                           [field-ctc (in-list (list #,@flat-ctc-lst))]
                           ; skip the instance name at the first element of the list
                           [field (in-list (cdr (dp-instance-fields a-inst)))])
                          ; error will be triggered below when predicate? is #f
                          (field-ctc field the-srcloc name
                                     (add-field-context/kc
                                      context
                                      (list-ref the-field-names i))
                                     predicate?)))
                      ; list of contracts constructed from value-dependent combinators
                      (define v-dep-ctc-lst
                        (map (λ (a-ctc-ctr) ; a contract constructor from value
                               (a-ctc-ctr a-inst))
                             (list #,@v-dep-ctc-lst)))
                      ; result is only used when predicate? is #t
                      (define v-dep-result
                        (for/and
                          ([i (range (length the-field-names))]
                           [field-v-dep-ctc (in-list v-dep-ctc-lst)]
                           ; skip the instance name at the first element of the list
                           [field (in-list (cdr (dp-instance-fields a-inst)))])
                          ; error will be triggered below when predicate? is #f
                          (field-v-dep-ctc field the-srcloc name
                                           (add-field-context/kc
                                            context
                                            (list-ref the-field-names i))
                                           predicate?)))
                      (if predicate?
                          ; assuming flat-result and v-dep-result are real Booleans
                          (and flat-result v-dep-result)
                          a-inst)))
                 
                 (define inst-ctc/c
                   #`(make-flat-contract
                        #:name 'instance
                        #:first-order
                        (λ (a-inst)
                          (and
                           (dp-instance? a-inst)
                           ((and/c
                             ; the instance name symbol got skipped
                             (list/c (un#@-in-template flat-ctc-lst))
                             ; value-dependent contract
                             (apply list/c
                                    (map (λ (a-ctc-ctr) ; a contract constructor from value
                                           (a-ctc-ctr a-inst))
                                         (list (un#@-in-template v-dep-ctc-lst)))))
                            ; skip the first field which is a symbol indicating the instance name
                            (cdr (dp-instance-fields a-inst)))))
                        #:late-neg-projection
                        (λ (blame)
                          (define flat-projs
                            (for/list ([i (range (length (syntax->datum #'#,instance-fields-name)))])
                              ((contract-late-neg-projection
                                (list-ref (list (un#@-in-template flat-ctc-lst)) i))
                               (add-field-context
                                blame
                                (list-ref (syntax->datum #'#,instance-fields-name) i)))))
                          (λ (a-inst neg-party)
                            ; first check if a-inst is an instance
                            ; this is a sanity check, should already be enforced with the
                            ; define- and create-instances
                            (when (not (dp-instance? a-inst))
                              (error "instance contract internal error"))
                            ; apply the projection on each field, resulted obeying values are discarded
                            ; any value violating the contract triggers the blame error in the projection
                            ; apply the non-value-dependent projections first
                            (for ([proj (in-list flat-projs)]
                                  [field (in-list (cdr (dp-instance-fields a-inst)))])
                              (proj field neg-party))
                            ; create the value-dependent projections from the instance passing the flat part
                            (define v-dep-projs
                              (for/list ([i (range (length (syntax->datum #'#,instance-fields-name)))])
                                ((contract-late-neg-projection
                                  (list-ref
                                   (map (λ (a-ctc-ctr) ; a contract constructor from value
                                          (a-ctc-ctr a-inst))
                                        (list (un#@-in-template v-dep-ctc-lst)))
                                   i))
                                 (add-field-context
                                  blame
                                  (list-ref (syntax->datum #'#,instance-fields-name) i)))))
                            ; apply the value-dependent projections later
                            (for ([proj (in-list v-dep-projs)]
                                  [field (in-list (cdr (dp-instance-fields a-inst)))])
                              (proj field neg-party))
                            a-inst))))

                 ; end of contracts

                 )
               
               ; define element type structs presented in instance fields               
               ; Begin -- old version (discard later)
               ; ---
               #;#,@(for/list ([a-field (free-id-table-keys parsed)])
                    (let ([an-el-type-to-make
                          (dp-stx-type-info-field (free-id-table-ref parsed a-field) el-type-to-make)])
                      (if (equal? an-el-type-to-make 'undefined)
                          #'(begin) ; Question: idiomatic way to specify no-op?
                          ; Question: why attaching the context of #'name is required 
                          ;#`(define #,(format-id #'name "~a" (hash-ref an-el-type-to-make 'type-name)) 1)
                          #`(r:struct #,(hash-ref an-el-type-to-make 'type-name)
                                      #,(hash-ref an-el-type-to-make 'attrs))
                          )))
               ; ---
               ; End of old version
               #,@(for/list ([a-el-type el-types-to-make])
                    #`(begin
                        (provide (struct-out #,(hash-ref a-el-type 'type-name)))
                        (r:struct #,(hash-ref a-el-type 'type-name)
                                  (id #,@(hash-ref a-el-type 'attrs))
                                  #:transparent
                                  ; Question: easy way to access {type-name}-{attrname}?
                                  ;#:methods gen:custom-write
                                  #;[(define write-proc
                                     (r:λ (the-el port mode)
                                          (fprintf port "[id:~a, ~a]")))])))
              
               
               ; define instance constructor with annotation of static syntax information
               ; contract checks at runtime instantiation
               (define-syntax (define/instance stx)
                 (syntax-parse stx
                   [(_ a-var-name
                       #;#,@(for/list ([a-field instance-field-lst])
                            (format-symbol "pv-~a" a-field))
                       ([field-name:id field-val] ...+))
                    #:with mtest (format-id #'a-var-name "test1")
                    #:with runtime-id (generate-temporary #'a-var-name)
                    ; (... ...) escapes to ... in the inner layer
                    #:with field-names #'(field-name (... ...))              
                    #:fail-when (not (equal? (length (syntax->list #'field-names))
                                             #,(length instance-field-lst)))
                                 "wrong number of fields given"
                    #:with field-vals-unsorted #'(field-val (... ...))
                    #:with field-vals
                           #`#,(let* ([input-names-lst (syntax->list #'field-names)]
                                      [input-vals-lst (syntax->list #'field-vals-unsorted)]
                                      [inst-field-lst instance-fields-name]
                                      [len (length input-names-lst)])
                                 (foldl
                                  (λ (i field-val-acc)
                                    (let ([idx
                                           (index-of
                                            inst-field-lst
                                            (list-ref input-names-lst i)
                                            ;free-identifier=?
                                            ; FIXME: the field names in importing files are not 
                                            ; free-identifier=? to the one in original defining file
                                            (λ (x y) (equal? (syntax-e x) (syntax-e y))))])
                                      (if idx
                                          (list-set
                                           field-val-acc
                                           idx
                                           (list-ref input-vals-lst i))
                                          (raise-syntax-error
                                           #f "no such field in the instance"
                                           (list-ref input-names-lst i)))))
                                  (make-list len #f)
                                  (range len)))
                           ; the below version is shorter
                           ; however, it does not detect wrong instance field
                           ; when the numbers of the fields are equal
                           #;#`#,(map
                                (λ (x)
                                  (list-ref
                                   (syntax->list #'field-vals-unsorted)
                                   (index-of (syntax->list #'field-names) x
                                             free-identifier=?)))
                                (syntax->list #'#,instance-field-lst))
                    
                    ; render the ```instance-field-lst''' at phase 1
                    ; from the outside into the template,
                    ; in the generated code, define it as ```field-lst'''
                    ; probably id becomes symbols
                    (define field-lst '#,instance-field-lst)
                    ;(define parsed #,parsed) -- not used anywhere

                    ; Not-In-Use (Moved, see ``contracts for instance objects above'')
                    ; instance contract generators
                    #;(define inst-ctc/c
                      #'(and/c
                         #,(for/list ([a-field instance-field-lst])
                         ; for every instance field, generate a contract given instance field lst (indices)
                         ; which the contract checks the whole instance value **instead of that field**
                             ; expect the ctc field is a procedure
                             ((dp-stx-type-info-field (free-id-table-ref parsed a-field) ctc)
                              instance-field-lst))))
                         ; Maybe:
                         ; (... ctc) should be a function returns a syntax object containing the contract
                    ; End of Not-In-Use
                    
                    (quasisyntax/loc stx
                        (begin
                          ; Begin debug use, to check what's in ctc-list
                          ;---
                          ;(pretty-print #'#,flat-ctc-lst)
                          ;(pretty-print (syntax-e #'#,v-dep-ctc-lst))
                          ;(define mtest (list-ref (list #,@v-dep-ctc-lst) 2))
                          ;---
                          ; End of debug use
                        
                          ; underying object of a-var-name:id
                          (define runtime-id
                            (contracted-v/kc
                             (un#-in-template inst-ctc/kc)
                             (dp-instance
                              (list 'instance
                                    ; escape to phase 1
                                    (un#@-in-template
                                     (let ([val-list (syntax->list #'field-vals)])
                                       ; field-lst defined above in phase 1
                                       (for/list ([i (range (length field-lst))]) 
                                         (list-ref val-list i))))))
                             (un#-in-template (syntax-srcloc stx))
                             'define/instance
                             (list "the instance to be defined (check the problem definition)")
                             ))
                          #;(define/contract runtime-id
                            ; inst-ctc/c defined a layer above
                            (un#-in-template inst-ctc/c)
                            (dp-instance
                             (list 'instance
                                  ; escape to phase 1
                                  (un#@-in-template
                                   (let ([val-list (syntax->list #'field-vals)])
                                     ; field-lst defined above in phase 1
                                     (for/list ([i (range (length field-lst))]) 
                                       (list-ref val-list i)))))))
                          ; attach static information of a-var-name:id
                          (define-syntax a-var-name
                            ; copy type description and change the underlying runtime id
                            (instance-type-annotate #'runtime-id)
                            ;#; expanded to:
                            ;-----------------------
                            #;(let ([the-type-info
                                     (syntax-local-value #'instance-type-info)])
                                ; copy type description and change underlying runtime id
                                (struct-copy
                                 type-info
                                 the-type-info
                                 [(un#-in-template (quote-syntax runtime-id) #'runtime-id)]))
                            ;----------------------
                            ;#;end of expanded to
                            )
                          ))]))

               ; construct a instance object value, resulting an expression
               ; FIXME: contains ``define'', might not be able to used in certain
               ; context as expression.
               ; Question: How to check a contract on an object it immediately
               ; and return the object as the value?
               (define-syntax create-instance
                 (func-type-info
                  (syntax-local-value #'instance-type-info)
                  (syntax-parser
                   [(create-?-instance ([field-name:id field-val] ...+))
                    #:with runtime-id (generate-temporary #'a-var-name)
                    ; (... ...) escapes to ... in the inner layer
                    #:with field-names #'(field-name (... ...))              
                    #:fail-when (not (equal? (length (syntax->list #'field-names))
                                             #,(length instance-field-lst)))
                                 "wrong number of fields given"
                    #:with field-vals-unsorted #'(field-val (... ...))
                    #:with field-vals
                           #`#,(let* ([input-names-lst (syntax->list #'field-names)]
                                      [input-vals-lst (syntax->list #'field-vals-unsorted)]
                                      [inst-field-lst instance-fields-name]
                                      [len (length input-names-lst)])
                                 (foldl
                                  (λ (i field-val-acc)
                                    (let ([idx
                                           (index-of
                                            inst-field-lst
                                            (list-ref input-names-lst i)
                                            ; FIXME: see the same place for define-instance
                                            (λ (x y) (equal? (syntax-e x) (syntax-e y))))])
                                      (if idx
                                          (list-set
                                           field-val-acc
                                           idx
                                           (list-ref input-vals-lst i))
                                          (raise-syntax-error
                                           #f "no such field in the instance"
                                           (list-ref input-names-lst i)))))
                                  (make-list len #f)
                                  (range len)))
                           ; FIXME: this and the field-lst above needs to be moved outside
                           ;        it might not keep the same type as now
                           (define field-lst '#,instance-field-lst)
                           (quasisyntax/loc (syntax-srcloc #'create-?-instance)
                             (contracted-v/kc
                              (un#-in-template inst-ctc/kc)
                              (dp-instance
                               (list 'instance
                                    ; escape to phase 1
                                     (un#@-in-template
                                      (let ([val-list (syntax->list #'field-vals)])
                                        ; field-lst defined above in phase 1
                                        (for/list ([i (range (length field-lst))]) 
                                          (list-ref val-list i))))))
                              (un#-in-template (syntax-srcloc #'create-?-instance))
                              'create-instance
                              (list "the instance to be created (check the problem definition)")
                              )
                             #;(contract ; inst-ctc/c defined a layer above
                              (un#-in-template inst-ctc/c)
                              (dp-instance
                               (list 'instance
                                     ; escape to phase 1
                                     (un#@-in-template (let ([val-list (syntax->list #'field-vals)])
                                                         ; field-lst defined above in phase 1
                                                         (for/list ([i (range (length field-lst))]) 
                                                           (list-ref val-list i))))))
                              'create-instance
                              'fields
                              'create-instance
                              (un#-in-template (syntax-srcloc #'create-?-instance))))
                           ])))
               

               ; discarded -- only one field for the certificate, attach no static info
               #|; nominal certificate contract
               (define (certificate/c x)
                 (and (list? x)
                      (equal? (list-ref x 0) 'certificate)))
               ; define certificate constructor with annotation of static syntax information
               (define-syntax (certificate stx)
                 (syntax-parse stx
                   [(_ a-var-name the-field)
                    #:with runtime-id (generate-temporary #'a-var-name)
                    ; why not (define the-ctc #,(....))?
                    ; 3d-syntax? store
                    (define the-ctc #'#,(dp-stx-info-field cert-parsed-type ctc))
                    #`(begin
                        
                        (define/contract runtime-id
                          (list/c symbol? #,the-ctc)
                          (list 'certificate the-field))

                        ; static information of a-var-name:id
                        (define-syntax a-var-name
                          (type-info 'certificate
                                     ; field name (symbol?) -> index (natural?)
                                     (hash)
                                     #'runtime-id))
                        )]))
               |#
               
               ; Begin debug use, to check what's in ctc-list
               ;---
               ;(pretty-print #'#,(dp-stx-info-field cert-parsed-type v-dep-ctc))
               ;---
               ; End of debug use

               (define (certificate/kc a-instance)
                 (and/kc
                  #,(stx-subst-with-id-table
                     (dp-stx-info-field cert-parsed-type ctc)
                     ctc-subst-tbl)
                  (#,(stx-subst-with-id-table
                      (dp-stx-info-field cert-parsed-type v-dep-ctc)
                      ctc-subst-tbl) a-instance)
                  ))
               
               ; field accessors  
               #,@(for/list ([i (range (length instance-field-lst))])
                    (let ([cur-field-name (list-ref instance-field-lst i)])
                        ; if ,cur-field-name is already defined (by another problem definition),
                        ; then nop
                        ; else define accessor ,cur-field-name
                        #`(void-if-id-presents
                           #,cur-field-name
                           (define-syntax (#,cur-field-name stx)
                            (syntax-parse stx

                              [(_ x:id)
                               (let ([the-type-info
                                      (syntax-local-value
                                       #'x
                                       (λ () ; if no local value, give out error according to the case
                                         (if (identifier-binding #'x)
                                             (raise-syntax-error
                                              #f
                                              "no type information available"
                                              stx
                                              #'x)
                                             (raise-syntax-error
                                              #f
                                              "unbounded identifier"
                                              stx
                                              #'x))))])
                                 (if (not
                                      (and (type-info? the-type-info)
                                           (hash? (type-info-idxes the-type-info))))
                                     ; incompatible static information
                                     (raise-syntax-error #f
                                                         "unknown type"
                                                         stx)
                                     (let ([idx (hash-ref
                                                 (type-info-idxes the-type-info)
                                                 '#,cur-field-name
                                                 #f)])
                                       (if idx
                                           #`(r:list-ref
                                              (dp-instance-fields #,(type-info-runtime-id the-type-info))
                                              #,idx)
                                           ; no such field
                                           (raise-syntax-error #f
                                                               "unsupported operation"
                                                               stx)))))]
                              ; TODO: refactor this case and above to remove duplicated code
                              [(_ (f:id arg (... ...)))
                               (let* ([the-func-type-info
                                       (syntax-local-value
                                        #'f
                                        (λ () ; if no local value, give out error according to the case
                                          (if (identifier-binding #'f)
                                              (raise-syntax-error
                                               #f
                                               "no type information available"
                                               stx
                                               #'x)
                                              (raise-syntax-error
                                               #f
                                               "unbounded identifier"
                                               stx
                                               #'x))))]
                                      [the-type-info
                                       (if (func-type-info? the-func-type-info)
                                           (func-type-info-ret-type the-func-type-info)
                                           (raise-syntax-error #f "unknown type" stx))])
                                 (if (not
                                      (and (type-info? the-type-info)
                                           (hash? (type-info-idxes the-type-info))))
                                     ; incompatible static information
                                     (raise-syntax-error #f
                                                         "unknown type"
                                                         stx)
                                     (let ([idx (hash-ref
                                                 (type-info-idxes the-type-info)
                                                 '#,cur-field-name
                                                 #f)])
                                       (if idx
                                           #`(r:list-ref
                                              (dp-instance-fields (f arg (... ...)))
                                              #,idx)
                                           ; no such field
                                           (raise-syntax-error #f
                                                               "unsupported operation"
                                                               stx)))))]
                              [self:id (raise-syntax-error #f "must be used on an instance" #'self)#;#'self])))))


               ; instance generator
               (define field-generator-lst ; indices aligned with ```field-lst'''
                 (list #,@(for/list ([a-field instance-field-lst])
                           (dp-stx-type-info-field (free-id-table-ref parsed a-field) generator)
                            )))

               (define/contract/kc (instance-generator)
                 (->k () instance/kc)
                 (dp-instance
                  (let rec ([retry-remaining 10])
                   ;(with-handlers ([exn:fail?
                   ;                (if (> retry-remaining 0)
                   ;                    (rec (- retry-remaining 1))
                   ;                    (error "failed to generate instance satisfying the invaraints"))])
                     (let rec-inst-part ([cur-inst (list 'instance)]
                                         [i 0])
                       (if (>= i (length field-generator-lst))
                           cur-inst
                           (let ([the-cur-field
                                  (((list-ref field-generator-lst i)
                                    ; intermediate instance, incomplete fields
                                    (dp-instance cur-inst)))])
                             (begin
                               (rec-inst-part (append cur-inst (list the-cur-field)) (+ i 1)))))
                       ))));)

               ; pretty-printer
               (define/contract/kc (inst-pretty-printer x)
                 (->k ([x instance/kc]) any/kc)
                 (displayln "--------------start-------------")
                 (displayln 'instance)
                 #,@(for/list ([i (range (length instance-field-lst))])
                      (let ([cur-field-name (list-ref instance-field-lst i)])
                        #`(begin
                            (display (format "~a:\n" '#,cur-field-name))
                            (pretty-print (list-ref (dp-instance-fields x) (+ #,i 1))))))
                 (displayln "---------------end--------------"))
               #;(define (inst-pretty-printer x)
                 (unless (instance/c x)
                   (raise-argument-error 'inst-pretty-printer (format "~a" 'instance) x))
                 (displayln "--------------start-------------")
                 (displayln 'instance)
                 #,@(for/list ([i (range (length instance-field-lst))])
                      (let ([cur-field-name (list-ref instance-field-lst i)])
                        #`(begin
                            (display (format "~a:\n" '#,cur-field-name))
                            (pretty-print (list-ref (dp-instance-fields x) (+ #,i 1))))))
                 (displayln "---------------end--------------"))

               (define (cert-pretty-printer x)
                 (pretty-print x))
               
               ; create define-verifier
               (define-syntax (define-verifier-id stx)
                 (syntax-parse stx
                   [(_ arg-inst:id arg-cert:id body ...+)
                    ; move ctx to the ctx of ```stx''' here.
                    ; Use verifier-id directly would cause unbounded identifier
                    #:with verifier-id-here
                           (format-id stx "~a" (syntax-e #'verifier-id))
                    ; define the id here
                    #:with solver-id-here (format-id stx "~a-solver" #'name)
                    #:with null-cert-here (format-id stx "~a" #'null-cert)
                    #:with yes/kc-here (format-id stx "yes-~a/kc" #'name)
                    #:with no/kc-here (format-id stx "no-~a/kc" #'name)
                    #:with checker-body
                           #`((define-syntax arg-inst
                                (instance-type-annotate #'arg-inst-runtime))
                              ; arg-inst:id appears in body will be recognized as
                              ; transformer binding define above

                              ; when the #'define-verifier-id for an actual problem expands
                              ; at the evaluation ``checker-body'', the expression inside #,@ evaluates
                              ; and filled in the template of #`(....)
                              ; the whole #,@(....) part is generated by the ``decision-problem''
                              #,@(dp-verifier-rewrite
                                  #'(body (... ...))
                                  (cons #'arg-cert
                                        ; #,(....) escapes when generating the
                                        ; #'define-verifier-id macro,
                                        ; the evaluated #,(....) will be part of the
                                        ; code of the #'define-verifier
                                                            
                                        ; uncomment below to see certificate kv-type for debugging
                                        #;(raise-syntax-error 'cert-type
                                           (dp-stx-info-field cert-parsed-type kv-type-object))

                                        #,(dp-stx-info-field cert-parsed-type kv-type-object)
                                        )
                                  (list
                                   #,@(for/list ([a-field instance-field-lst])
                                        ; key the ``cons'' in the code
                                        ; fill in the two positions in the template #`(cons #'$pos1 $pos2)
                                        ; with the result of evaulating expression inside #,(....)
                                        ; the expression inside #,(....) is evaluated in the phase 1
                                        ; related to the position of ``decision-problem''
                                        #`(cons #'#,a-field
                                                #,(dp-stx-type-info-field
                                                   (free-id-table-ref parsed a-field)
                                                   kv-type-object))))
                                  ))
                    #`(begin

                        
                        (provide verifier-id-here
                                 solver-id-here
                                 null-cert-here
                                 yes/kc-here
                                 no/kc-here)

                        
                        ; verifier interface with contract exposed to the user
                        (define/contract/kc (verifier-id-here arg-inst-runtime arg-cert)
                          (->k ([the-inst instance/kc]
                                [the-cert (the-inst) (certificate/kc the-inst)])
                               any/kc) ; should we enforce boolean? here?
                          (r-checker-for-verifying arg-inst-runtime arg-cert))

                        ; verifier to feed the solver (not protected with contracts)
                        ; Begin -- expected expanded to for verifying (not solving)
                        ; -----------------
                        #;(define (r-checker arg-inst-runtime arg-cert)                         
                            (define-syntax arg-inst
                              (instance-type-annotate #'arg-inst-runtime))
                            ; arg-inst:id appears in body will be recognized as
                            ; transformer binding define above
                            body (... ...))
                        ; End of -- expected expaned to
                        (define (r-checker-for-verifying arg-inst-runtime arg-cert)
                          ; #'checker-body exists in phase 1
                          #,@#'checker-body)
                        (define (r-checker-for-solving arg-inst-runtime arg-cert)
                          (syntax-parameterize ([dp-solver-env? #t])
                            #,@#'checker-body))

                        ; deriving the solver
                        (define/contract/kc (solver-id-here a-instance)
                          (->k ([x instance/kc]) any/kc)
                          ; annotate type information to the instance-id-with-type-info
                          (define-syntax instance-id-with-type-info
                            (instance-type-annotate #'a-instance))


                          ; Not-In-Use : old sym-cert creation
                          ; -----------
                          #;(define cert-hash-keys
                            ; ``rendering'' expects a syntax object and unescapes the syntax object
                            ; #, -- render on layer 0 the content generated by
                            ;       the following expression on layer 1
                            ; #' -- what follows is a syntax object on this layer (layer 1)
                            ; #,(dp-stx-info-field cert-parsed-type upstream)
                            ;    -- render on layer 1 the content generated by
                            ;       the following expression on layer 2
                            ;   We know that (eq?
                            ;                   (syntax? (dp-stx-info-field cert-parsed-type upstream)
                            ;                 #t)
                            #;
                            #,
                            #'
                            #,(dp-stx-info-field
                               (dp-stx-info-field cert-parsed-type upstream)
                               upstream)
                            ;end

                            #,#'#,(let loop ([cur-layer cert-parsed-type])
                                  (if (identifier?
                                       (dp-stx-info-field cur-layer upstream))
                                      #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                         (#,(dp-stx-info-field cur-layer upstream)
                                          instance-id-with-type-info))
                                      #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                         #,(loop (dp-stx-info-field cur-layer upstream))))))

                          ;(displayln cert-hash-keys) -- for debug

                          #;(define sym-cert
                            (for/hash ([v cert-hash-keys])
                              (values v (fresh-symbolic-bool))))
                          ;-----------
                          ; End of Not-In-Use

                          ; Begin debug use, check the base of symbolic-cert
                          ; ---------
                          #;(define sym-cert-base
                            #,#'#,(let loop ([cur-layer cert-parsed-type])
                                    (if (identifier?
                                         (dp-stx-info-field cur-layer upstream))
                                        #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                           (#,(dp-stx-info-field cur-layer upstream)
                                            instance-id-with-type-info))
                                        #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                           #,(loop (dp-stx-info-field cur-layer upstream))))))
                          ;(pretty-print "cert-base")
                          ;(pretty-print sym-cert-base)
                          ; ----------
                          ; End of debug use


                          ;
                          ; Not-In-Use : old sym-cert creation
                          ;---------------------------------------------------
                          #;(define sym-cert
                            #,#'(#,(dp-stx-info-field cert-parsed-type symbolic-accessor)
                                 ; XXX: this is a temporary solution that only take cares of
                                 ; the outmost layer if upstream is a list
                                 ; the #,@ immediately below is because symbolic-accessor with
                                 ; takes multiple arguments instead of a list when upstream is a list
                                 #,@(if (list? (dp-stx-info-field cert-parsed-type upstream))
                                        (map
                                         (λ (x)
                                           #`(#,x instance-id-with-type-info))
                                         (dp-stx-info-field cert-parsed-type upstream))
                                        ; wrap the resulting syntax in a list to accommondate the #,@
                                        #`(#,(let loop ([cur-layer cert-parsed-type])
                                               (if (identifier?
                                                    (dp-stx-info-field cur-layer upstream))
                                                   #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                                      (#,(dp-stx-info-field cur-layer upstream)
                                                       instance-id-with-type-info))
                                                   #`(#,(dp-stx-info-field cur-layer upstream-accessor)
                                                      #,(loop (dp-stx-info-field cur-layer upstream)))))))))

                          #;(define struct-constr-lst
                            (if (has-struct-constr? sym-cert)
                                (struct-constr sym-cert)
                                '()))
                          ;
                          ;----------------------------------------------
                          ; End of Not-In-Use

                          (define sym-cert-constr
                            (#,#'#,(dp-stx-info-field cert-parsed-type symbolic-constructor) a-instance))

                          
                          (define-values (sym-cert struct-constr-lst) (sym-cert-constr))
                          
                          ; (DONE): incooporated in structural constraint 
                          ; TODO: derive certificate structural constraint (maybe instance value-dependent)
                          ;       specified in the problem definition
                          ;       e.g. ```#:size N''' in
                          ;            ```#:certificate (set #:of-type element #:size N)'''
                          ;            where N is an instance field
                          ; (define (check-cert-constr a-cert)
                          ;         (cert-cstr-from-definition a-instance))
                          ;


                          ;
                          ; Note: the assert below needs to resides in ``solve'',
                          ;       in some cases the symbolic executioner can know
                          ;       the constraint unsatisifable before coming up with
                          ;       a formula to be sent to the solver. In such cases we
                          ;       will get assertion failure exception. ``solve'' instead
                          ;       turns such assertion failure inside to (unsat).
                          ;
                          ;       However, we will not be able to distinguish incorrect
                          ;       programs (e.g. w/ function calls of mismatching arguments,
                          ;       hash-ref a nonexisting key) from such cases.
                          ;       The implemented type system partially solved the problem. 
                          ;       
                          ;       To get the content of assertion store for debugging,
                          ;       follow the comment instruction
                          ;
                          (define solution ; -- comment out this line for debugging
                            (r:solve       ; -- comment out this line for debugging
                             
                             (r:assert   ; run the checker on symp-cert and add constraints to solver
                              ;(pretty-print ; for further debugging, kept in comment in normal use
                               (r:and
                               ; (DONE) TODO: add certificate structural constraint
                               ;              specified in the problem definition (See above)
                               ; (check-cert-constr sym-cert)
                               (r:andmap
                                (r:λ (pred)
                                     (pred sym-cert))
                                struct-constr-lst)
                               (r-checker-for-solving
                                a-instance
                                sym-cert))) ; leave the paren on this line to match pretty-print
                             
                             )) ; -- comment out this line for debugging

                          ;(pretty-print (r:vc)) ;-- for debugging, kept in comment in normal use

                          #;(define solution ; for debugging, kept in comment in normal use
                              (r:solve
                             #t)) ; solve constraints already in assert store, nothing new to add

                          ;(pretty-print sym-cert) ;-- for debugging, kept in comment in normal use
                          ;(pretty-print (r:model solution)) ;-- for debugging, kept in comment in normal use

                          (r:clear-state!) ; clear Rosette assertion store,
                                           ; clear Rosette symbolic heap,
                                           ; i.e. release all symbolic variable
                                           ; created with ``fresh-symbolic-xxx'' 
                                           ; by ``sym-cert-constr'' above
                                           ; note: this reset current-solver to z3
                                           ; (why this directive is not in Rosette doc ?)                         

                          ; encode the hash solution to certificate type object
                          (#,#'#,(dp-stx-info-field cert-parsed-type solution-decoder) sym-cert solution))
                        
                        (define null-cert-here
                          #,#'#,(dp-stx-info-field cert-parsed-type null-object))
                        ; contract for yes and no instance of the problem
                        (define yes/kc-here
                          (yes-instance/kc instance/kc
                               solver-id-here
                               null-cert-here
                               ;#,#'#,(dp-stx-info-field cert-parsed-type null-object)
                               ))
                        (define no/kc-here
                          (no-instance/kc instance/kc
                               solver-id-here
                               null-cert-here
                               ;#,#'#,(dp-stx-info-field cert-parsed-type null-object))
                          )) 
                        )]))               
               
               
               ; for debugging use, output everything in the parsing table
               #;#,(for/hash ([(k v) (in-free-id-table parsed)])
                   (values k (syntax-property v 'type-info)))       
               ) ;end of begin 
           )
         )]))


  )
