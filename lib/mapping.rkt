#lang racket

(require
  (prefix-in r: rosette/safe)

  "../private/primitive-data-type.rkt"
  "../private/problem-definition-core.rkt"
  "../private/karp-contract.rkt"
  [for-syntax racket/syntax
              racket/struct
              syntax/parse
              syntax/id-table
              racket/match]
  [for-meta 2 racket/base
              syntax/parse])

(provide
 (struct-out dp-mapping)
 dp-mapping/c
 dp-mapping-d/c
 dp-mapping/kc
 dp-mapping-d/kc
 mapping
 lookup-safe
 lookup
 dom

 dp-symbolic-mapping
 dp-mapping-from-sol)

; type object representing mappings
(begin-for-syntax
  (provide tMapping)

  (struct ty-Mapping (dom-type rng-type)
    #:transparent
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Mapping)
        (λ (self) (list (ty-Mapping-dom-type self)
                        (ty-Mapping-rng-type self)))))]
    )

  (define-match-expander tMapping
    (syntax-parser
      [(_ dom-type rng-type) #'(ty-Mapping dom-type rng-type)])
    (syntax-parser
      [(_ dom-type rng-type) #'(ty-Mapping dom-type rng-type)]))
)


; mapping structure
; H : (hash/c any/c any/c #:flat? #t), hash from domain element to an index of a ind-cod element
; el-rep : any/c, representative element. It is supposed to be #f when values are non-mergeable
;                 For mergeables, el-rep should be a value with complete hash keys
; defined : always #f, used to store intermmediate results during the construction of the mapping in reduction

; fallback to use Racket struct, see dp-set
(struct dp-mapping (H el-rep defined) #:transparent
          #:property prop:interface
          (r:list (r:cons 'symbolic?
                          (λ (the-map)
                            (if (not (dp-mapping-H the-map))
                                #f
                                (dp-symbolic?
                                 (hash-iterate-value
                                  (dp-mapping-H the-map)
                                  (hash-iterate-first (dp-mapping-H the-map))
                                  #f))))))
          #:property prop:procedure
          (r:λ (the-mapping k)
               (if (dp-symbolic? k)
                   (raise "the domain element referred in mapping can not contains value to be solved")
                   (hash-ref (dp-mapping-H the-mapping) (dp-wrap-if-raw-int k))))
          #:methods gen:custom-write
          [(define write-proc
             (r:λ (the-map port mode)
                  (if (dp-mapping-H the-map)
                      (fprintf port "[\n ~a \n]"
                               (string-join
                                (for/list ([(k v) (in-hash (dp-mapping-H the-map))])
                                  (format "~a ~~> ~a" k v))
                                "\n "))
                      (fprintf port "null (no solution)"))))]
          #:methods gen:dp-mergeable
          ; M-rep is the representative mapping, share the same hash keys as one of the mappings in the union
          [(define (gen-merge-union U-maps M-rep)
             (let* ([H (dp-mapping-H M-rep)]
                    [merge-func (if (dp-mergeable? (car (hash-values H)))
                                    gen-merge-union
                                    (λ (x y) x))])
               (dp-mapping
                (for/hash ([k (hash-keys H)])
                  (values
                   k
                   (merge-func (r:for/all ([Mx U-maps])
                                          (hash-ref (dp-mapping-H Mx) k))
                               (dp-mapping-el-rep M-rep)))
                  ; take the representative element of the representative mapping
                  (dp-mapping-el-rep M-rep)
                  #f))))
           (define (gen-representative-el-from-lst M-lst dummy-mapping)
             (let ([a-mapping (car M-lst)])
               (dp-mapping (for/hash ([k (hash-keys (dp-mapping-H a-mapping))])
                             ; do not care the hash value
                             ; XXX: the hash value of a-mapping might be symbolic
                             ; which better not be placed here directly
                             ; this is why el-rep has contract any/c
                             (values k #t))
                           (let ([vs (hash-values (dp-mapping-H a-mapping))])
                             (if (dp-mergeable? (car vs))
                                 (gen-representative-el-from-lst
                                  vs
                                  (car vs))
                                 #f))
                           #f)))
           (define gen-decode-merged-from-sol
             (λ (M-merged sol)
               (dp-mapping-from-sol
                M-merged
                dp-element-from-sol
                sol)))])




(define (sym-hash-ref htbl hk-lst x)
  (if (empty? hk-lst)
      (error "key not exists")
      (r:if (r:equal? x (car hk-lst))
            (hash-ref htbl (car hk-lst))
            (sym-hash-ref htbl (cdr hk-lst) x))))

; selective compile to efficent version / safe version
(provide lookup-typed-rewriter)
(define-syntax lookup-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ (_ (tMapping τb-k τb-v)) ('CON τb-k))
       (syntax-parser
         [((~optional lookup) a-mapping key) (cons #'(a-mapping key) τb-v)])]
      [(args-τ (_ (tMapping τb-k τb-v)) ('SYM b-k))
       (syntax-parser
         [((~optional lookup) a-mapping key) (cons #'(lookup-safe a-mapping key) τb-v)])]
      [(args-τ (_ (tMapping τb-k τb-v)) ('SYM τb-k2))
       (syntax-parser
         [((~optional lookup) a-mapping key) (raise-syntax-error #f
                              (format "domain element type mismatch: expects ~a, gets ~a"
                                      τb-k τb-k2)
                              #'(a-mapping key) #'key)])]
      [_ (syntax-parser
           [(m arg0 ...)
            (raise-syntax-error #f
                                (format "invalid operation ~a" type-lst)
                                #'(m arg0 ...))])])))

(define (lookup-safe a-mapping k)
  (let* ([H (dp-mapping-H a-mapping)]
         [first-v (car (hash-values H))]
         [merge-func (if (dp-mergeable? first-v)
                         gen-merge-union
                         (λ (x y) x))])
    (merge-func (sym-hash-ref H (hash-keys H) k)
                (dp-mapping-el-rep a-mapping))))


; domain accessor
(kv-func-type-annotate dom ((tMapping τb-d τb-r) (tSetOf τb-d)))
(define/contract/kc (dom a-mapping)
  (->k ([m (dp-mapping/kc any/kc any/kc)]) any/kc)
  (dp-list->set (hash-keys (dp-mapping-H a-mapping))))

(define/contract/kc (lookup a-mapping k)
  (->k ([m (dp-mapping/kc any/kc any/kc)]
        [k (m) (make-simple-contract/kc (v)
               (set-∈ v (dom m))
               (format "expects an element in the domain of ~e" m))]) any/kc)
  (if (dp-symbolic? k)
      (raise "the domain element referred in mapping can not contains value to be solved")      
      (hash-ref (dp-mapping-H a-mapping) (dp-wrap-if-raw-int k))))

; contract combinator for mapping
; with domain (from) elements and range (to) elements satisfying given contract, internal
; Note: flat version, key and value contracts are also flat
;       used to check only structure without value dependency
; See also: dp-setof/c
(define (dp-mapping/c from/c to/c)
  (and/c
   (struct/c dp-mapping
             (hash/c from/c to/c #:flat? #t)
             any/c ; XXX: this is not ideal
             ; what is equivalent to (equal?/c #f) ?
             (one-of/c #f))
   (λ (a-map)
     (andmap
      to/c
      (hash-values (dp-mapping-H a-map))))))

(define (mapping-dom-rng/kc from/kc to/kc)
  (kc-contract (a-mapping the-srcloc name context [predicate? #f])
     (let ([res
         (and
          (andmap
           (λ (k)
             (from/kc k the-srcloc 'mapping (cons "an element in the domain" context) predicate?))
           (hash-keys (dp-mapping-H a-mapping)))
          (andmap
           (λ (k)
             (to/kc (hash-ref (dp-mapping-H a-mapping) k)
                    the-srcloc 'mapping (cons (format "the image of ~e" k) context) predicate?))
           (hash-keys (dp-mapping-H a-mapping))))])
       (if predicate?
           (if res #t #f)
           a-mapping))))

(define (dp-mapping/kc from/kc to/kc)
  (and/kc
   (make-simple-contract/kc (v)
     (dp-mapping? v)
     "expects a mapping")
   (make-simple-contract/kc (v)
     ((struct/c dp-mapping
       (hash/c any/c any/c #:flat? #t)
        any/c ; XXX: this is not ideal
               ; what is equivalent to (equal?/c #f) ?
        (one-of/c #f)) v)
      "invalid mapping structure")
   (mapping-dom-rng/kc from/kc to/kc))
  )

; construct a contract factory for contract of mapping
; with domain (from) elements and range (to) elements satisfying specific contracts, internal
; Note: value-dependent version, produce a factory accepting dependent values
;       only checks if each key and each value satisfiying specific properties
;       does not check the domain or range as a whole
; See also: dp-setof-d/c
; from-ctc-d : (-> any/c ... (-> any/c boolean?)), contract of the domain element
; to-ctc-d : (-> any/c ... (-> any/c boolean?))
; -> (-> any/c ... (any/c -> boolean?))
(define ((dp-mapping-d/c from-ctc-d to-ctc-d) v . rest) ; curried shorthand
  ; produce contract of key/value given dependent values
  (let ([from-ctc (apply from-ctc-d (cons v rest))]
        [to-ctc (apply to-ctc-d (cons v rest))])
    (λ (a-map)
      (let ([H (dp-mapping-H a-map)])
        (andmap
         (λ (k)
           (and (from-ctc k)
                (to-ctc (hash-ref H k))))
         (hash-keys H))))))

(define ((dp-mapping-d/kc from-ctc-d to-ctc-d) v . rest)
  (let ([from-ctc (apply from-ctc-d (cons v rest))]
        [to-ctc (apply to-ctc-d (cons v rest))])
    (mapping-dom-rng/kc from-ctc to-ctc)))

; create a solvable symbolic mapping from domain to codomain, internal, non-solvable(?)
(define (dp-symbolic-mapping from-set to-symbolic-constr)
  (let*-values
      ([(assoc-k-sym-obj assoc-to-cstrs)
        (for/lists (sym-objs cstrs)
                   ([k (dp-set-members->list from-set)])
          (let-values ([(v cstr) (to-symbolic-constr)]) ; potentially can be (to-symbolic-constr k)
            ; Note: cstr is a list
            (values (cons k v) (cons k cstr))))]
       [(hash-sym-obj hash-cstr)
        (values (make-immutable-hash assoc-k-sym-obj) (make-immutable-hash assoc-to-cstrs))])
    (values
     (dp-mapping
      hash-sym-obj
      (if (dp-mergeable? (car (hash-values hash-sym-obj)))
          (gen-representative-el-from-lst (hash-values hash-sym-obj) (car (hash-values hash-sym-obj)))
          #f)
      #f)
     (r:list
      (r:λ (a-mapping)
           (r:andmap
            (r:λ (k)
                 (r:andmap
                  ; Note: (hash-ref hash-cstr k) is a list as cstr above is a list
                  ; for every constraint ``a-cstr'' (represented as a predicate) in the list
                  (r:λ (a-cstr)
                       ; apply it to the hash value
                       (a-cstr (hash-ref (dp-mapping-H a-mapping) k)))
                  (hash-ref hash-cstr k)))
            (hash-keys (dp-mapping-H a-mapping))))))))

(define dp-null-mapping (dp-mapping #f #f #f))

(define (dp-mapping-from-sol the-sym-mapping image-from-sol a-sol)
  (if (r:unsat? a-sol) dp-null-mapping
      (let* ([domain (hash-keys (dp-mapping-H the-sym-mapping))]
             [H (for/hash ([k domain])
                  (values k
                          (image-from-sol
                           (hash-ref
                            (dp-mapping-H the-sym-mapping)
                            k)
                           a-sol)))])
        (dp-mapping
         H
         (if (dp-mergeable? (car (hash-values H)))
             (gen-representative-el-from-lst (hash-values H) (car (hash-values H)))
             #f)
         #f))))


; #:from must be a set value
; #:to-type can be any type
(define-syntax (mapping stx)
  (if (dp-parse-table)
      (syntax-parse stx
        [(_ (~seq #:from (~or (~and ((~literal the-set-of) ~! _) set-of)
                              a-sth))
            (~seq #:to (~or ((~literal the-set-of) the-type)
                                                concrete-set))
            ; XXX: temp patch
            (~optional (~and #:disjoint pv-disjoint-sets?)))
         #:fail-when (attribute set-of) "domain can only be a concrete set"
         #`(mapping #:from a-sth #:to-type
                    #,(if (attribute concrete-set)
                          #'(element-of concrete-set)
                          #'the-type)
                    ; XXX: temp patch
                    (~? pv-disjoint-sets?))]
        [(_ (~seq #:from (~or from-set-name:id setlike-value))
            (~seq #:to-type type-desc)
            (~optional (~and #:disjoint pv-disjoint-sets?)))
         (let* ([from-set-temp-name (if (attribute from-set-name)
                                        #'from-set-name
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
                      from-set-temp-name
                      maybe-parsed-setlike-value)
                     (dp-parse-table))]
                [from-set-entry (free-id-table-ref parsed from-set-temp-name #f)]
                [from-set-type
                 (if from-set-entry
                     (parsed-entry-type from-set-entry)
                     (raise-syntax-error
                      #f
                      "undefined domain"
                      #'from-set-name))]
                [from-set-idx
                 (parsed-entry-idx from-set-entry)]
                [from-el-type
                 (let ([from-el-type (dp-stx-type-info-data-ref
                                      from-set-type
                                      'el-type)])
                   (if (equal? from-el-type 'undefined)
                       ; a set-like must have ''element type'' in type-info
                       (raise-syntax-error
                        #f
                        "not a valid set as the domain"
                        #'from-set-name)
                       from-el-type))]
                [from-ctc (dp-stx-info-field from-el-type ctc)]
                [from-v-dep-ctc (dp-stx-info-field from-el-type v-dep-ctc)]
                [from-upstream (if maybe-parsed-setlike-value
                                   (dp-stx-type-info maybe-parsed-setlike-value)
                                   #'from-set-name)]
                [from-accessor (dp-stx-type-info-accessor-ref from-set-type 'set)]
                ; XXX: temporary patch here
                [to-el-part
                  (dp-expand-part #'type-desc)]
                [to-el-type
                 (dp-stx-type-desc to-el-part)]
                [to-ctc (dp-stx-info-field to-el-type ctc)]
                [to-v-dep-ctc (dp-stx-info-field to-el-type v-dep-ctc)]
                ; XXX: temporary patch here
                [mapping-ctc
                 (if (attribute pv-disjoint-sets?)
                     (if
                      ;(raise-syntax-error #f (dp-stx-type-desc-data-ref to-el-part 'el-type))
                      ;(raise-syntax-error #f (assoc 'el-type (dp-stx-type-desc-field to-el-part type-data)))
                      (equal? (dp-stx-type-desc-data-ref to-el-part 'el-type) 'undefined)
                      (raise-syntax-error
                       #f
                       "disjoint can only be used on sets"
                       #'type-desc)
                      #`(and/kc
                         (dp-mapping/kc #,from-ctc #,to-ctc)
                         (make-simple-contract/kc (m)
                           (andmap
                            (λ (k1)
                              (andmap
                               (λ (k2)
                                 (implies
                                  (not (dp-equal? k1 k2))
                                  (dp-equal?
                                   (set-size
                                    (set-∩ (hash-ref (dp-mapping-H m) k1)
                                           (hash-ref (dp-mapping-H m) k2)))
                                   0)))
                               (hash-keys (dp-mapping-H m))))
                            (hash-keys (dp-mapping-H m)))
                            "expects an mapping whose elements in range are disjoint")))
                     #`(dp-mapping/kc #,from-ctc #,to-ctc))]
                ; end of temporary patch
                [mapping-v-dep-ctc #`(λ (a-inst)
                                       (and/kc
                                        ; domain constraints
                                        ; all mappings are total now
                                        (make-simple-contract/kc (a-mapping)
                                          (set-equal?
                                           (dom a-mapping)
                                           (#,from-accessor
                                            #,(trace-upstream-to-field from-upstream #'a-inst)))
                                          (format "expects a mapping with domain equals to ~e"
                                            (#,from-accessor
                                             #,(trace-upstream-to-field from-upstream #'a-inst))))
                                        ; for partial mapping -- not in use
                                        ; the domain is reflected on field defined
                                        #;(if (dp-mapping-defined a-mapping)
                                              (set-equal?
                                               (dp-list->set (hash-keys (dp-mapping-H (dp-mapping-defined a-mapping))))
                                               (#,from-accessor
                                                #,(trace-upstream-to-field from-upstream #'a-inst)))
                                              #t)
                                        ;---------
                                        ; end of not-in-use
                                          
                                        ; element-type constraint
                                        ((dp-mapping-d/kc #,from-v-dep-ctc #,to-v-dep-ctc) a-inst)))]
                [to-type-symbolic-constructor (dp-stx-info-field to-el-type symbolic-constructor)]
                [to-type-solution-decoder (dp-stx-info-field to-el-type solution-decoder)]
                ; ids in referred parts
                [to-type-desc-ids (dp-stx-info-field to-el-type referred-ids '())])
           (dp-stx-type-desc (generate-temporary #'mapping)
                             type 'mapping
                             kv-type-object #;(tMapping (tSymbol) (tBool))
                             #`(tMapping #,(dp-stx-info-field from-el-type kv-type-object)
                                         #,(dp-stx-info-field to-el-type kv-type-object))
                             atomic? #f
                             upstream from-upstream
                             upstream-accessor from-accessor
                             ctc mapping-ctc
                             v-dep-ctc mapping-v-dep-ctc
                             el-type-to-make (dp-stx-info-field to-el-type el-type-to-make)
                             type-data '()
                             accessors '()
                             generator #`(λ (a-inst)
                                           (λ ()
                                             (let* ([domain-set
                                                    (#,from-accessor
                                                     #,(trace-upstream-to-field from-upstream #'a-inst))]
                                                    [el-gen (#,(dp-stx-info-field to-el-type generator) a-inst)]
                                                    [H (for/hash ([el (dp-set-members->list domain-set)])
                                                        (values el (el-gen)))]
                                                    [vs (hash-values H)])
                                               (dp-mapping
                                                H
                                                (if (dp-mergeable? (car vs))
                                                    (gen-representative-el-from-lst
                                                     vs
                                                     (car vs))
                                                    #f)
                                                #f))))
                             symbolic-constructor (if (equal? to-type-symbolic-constructor 'undefined)
                                                      'undefined
                                                      #`(λ (a-inst)
                                                          (λ ()
                                                            (dp-symbolic-mapping
                                                             (#,from-accessor
                                                              #,(trace-upstream-to-field from-upstream #'a-inst))
                                                             (#,to-type-symbolic-constructor a-inst))
                                                           )))
                             solution-decoder (if (equal? to-type-symbolic-constructor 'undefined)
                                                  'undefined
                                                  #`(λ (the-sym-mapping sol)
                                                      (dp-mapping-from-sol
                                                       the-sym-mapping
                                                       #,to-type-solution-decoder
                                                       sol)))
                             null-object #'dp-null-mapping
                             referred-ids (append
                                           (if (attribute from-set-name) (list #'from-set-name) '())
                                           to-type-desc-ids)))])
      (syntax-parse stx
        ; TODO: check if k, v is symbolic
        [(_ (k (~datum ~>) v) ...)
         #'(dp-mapping (make-immutable-hash (list (cons (dp-wrap-if-raw-int k)
                                                        (dp-wrap-if-raw-int v)) ...))
                       ; XXX : assuming intention is given by the first element
                       ;       i.e., whether it is used as a set or as an abstract element
                       (if (dp-mergeable? (car (list v ...)))
                           (gen-representative-el-from-lst (list v ...) (car (list v ...)))
                           #f)
                       #f)]))
  )
