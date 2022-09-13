#lang racket

(require
  "private/core-structures.rkt"
  "private/primitive-data-type.rkt"
  [rename-in "private/decision-problem.rkt"
             (define dp-define)]
  ; TODO(?): move this to decision-problem,
  ;          so that everything comes from decision problem
  [only-in "private/dp-type-info.rkt" func-type-info]
  "private/karp-contract.rkt"

  [only-in racket/list
           (argmax lst-argmax)
           (argmin lst-argmin)]

  racket/require
  racket/require-syntax
  [prefix-in r: rosette]
  [for-syntax racket/list
              syntax/parse
              racket/syntax
              syntax/id-table
              syntax/to-string]
  racket/stxparam
  racket/syntax-srcloc
  #;[for-meta 2 racket/base
              syntax/parse
              racket/syntax])


 ; non-conflict require
(provide union-in)

(begin-for-syntax
  (define-syntax-class mod-name
    (pattern _:id)
    (pattern _:str))
  )

(define-require-syntax (union-in stx)
  (syntax-parse stx
    [(_ m1:mod-name m2:mod-name)
     #'(combine-in m1
                   (subtract-in m2 m1))]))


(provide
 [except-out (all-from-out "private/core-structures.rkt"
                           "private/primitive-data-type.rkt")
              natural
              set-∈-safe
              set-∉-safe
              dp-symbolic-subset
              dp-set-from-sol]

 ; custom define
 [rename-out (dp-define define)]
)

(provide check-reduction)
;




; not exactly duplicate with the one in decision problem, maybe combine them?
(begin-for-syntax
  
  (define (stx-subst-id stx old new)
    (syntax-parse stx
      [x:id (if (free-identifier=? #'x old) new #'x)]
      [(x) #:with res (stx-subst-id #'x old new)
           #'(res)]
      [(x y ...+) #:with res-first (stx-subst-id #'x old new)
                  #:with res-rest (stx-subst-id #'(y ...) old new)
                  (syntax-parse #'(res-first res-rest) ;syntax-cons?
                    [(z (w ...)) #'(z w ...)])
                  ]
      [anything-else #'anything-else]))
)


; abstract elements with subscripts
(provide el
         el?
         _1s
         _2s
         _3s
         _ks
         n_s
         index-in
         element-of-index
         ; TODO: remove the one below after testing
         dp-set-element-index
         )

(struct el-struct (subscripts) #:transparent
   #:methods gen:custom-write
  [(define write-proc
     (λ (the-el port mode)  
       (fprintf port "<~a>"
                (string-join
                 (for/list ([s (el-struct-subscripts the-el)])
                   (format "~a" s))
                 ", "))))])

(define-syntax (el stx)
  (syntax-parse stx
    [(_ subscript0 ...+)
     #'(el-struct (list (dp-wrap-if-raw-int subscript0) ...))]))

(define (el? a-sth)
  (el-struct? a-sth))

; first subscript
(define (_1s a-el)
  (list-ref (el-struct-subscripts a-el) 0))

; second subscript
(define (_2s a-el)
  (list-ref (el-struct-subscripts a-el) 1))

; third subscript
(define (_3s a-el)
  (list-ref (el-struct-subscripts a-el) 2))

; k-th subscript
(define (_ks a-el k)
  ; TODO: require k to be a constant
  (list-ref (el-struct-subscripts a-el) (- k 1)))

; length of subscript
(define (n_s a-el)
  (length (el-struct-subscripts a-el)))




; set comprehension and constructors
(provide for/set
         define/sets
         ;foreach/set
         find-one
         argmax
         argmin
         arg-kth-max
         arg-kth-min
         find-all
         all-pairs-in
         all-triplets-in
         corr
         curr

         ints-from-to)

; chaperone property for correspondence
(define-values (prop:corr has-corr? corr)
    (make-impersonator-property 'correspondence))

(begin-for-syntax
  (define-syntax-class element-of-a-set
    #:datum-literals (∈ in)
    #:description "an element from a set"
    (pattern [(~or x:id (x:id #:index ind:id)) (~or ∈ in) X:expr]
             #:attr indx (if (attribute ind) #'ind #'i)))
  )

; used to refer to the object in progress
(define-syntax-parameter curr
  (lambda (stx)
    (raise-syntax-error #f "can not be used outside mapping or for/set" stx)))

; indices of elements in a set
; starts with 1
; should not be used in solver
(define (dp-set-element-index a-set)
  (let ([mem-list (dp-set-members->list a-set)])
    (make-immutable-hash
     (map
      (λ (v)
        (cons v
              (dp-int-wrap (+ (index-of mem-list v) 1) 'poly)))
      mem-list))))

(define/contract/kc (index-in e a-set)
  (->k ([e any/kc] [a-set dp-set/kc]) any/kc)
  ; XXX: unfortunately we can not tell if the result is constant or poly
  ;      unless we know whether a-set is constant
  (hash-ref (dp-set-element-index a-set) (dp-wrap-if-raw-int e)))

(define/contract/kc (element-of-index i a-set)
  (->k ([i (and/kc
            (dp-natural-w/kc #f)
            (make-simple-contract/kc (v)
              (dp-int-ge v 1)
              "index needs to be at least 1")
            dp-int-not-exp-size/kc)]
        [a-set dp-set/kc]) any/kc)
  (list-ref (dp-set-members->list a-set) (- (dp-int-unwrap i) 1))
  ; TODO: change this to contract checking
  #;(if (dp-int-not-exp-size/c i)
      (list-ref (dp-set-members->list a-set) (- (dp-int-unwrap i) 1))
      (error "can not access an index expoential to the input length")))


; old version
(define-syntax for/set-old
  (syntax-parser
      [(_ {x-ind-expr (~datum for) x-in-X:element-of-a-set
                (~optional (~seq (~datum if) pred-x-ind))})
       #`(dp-list->set
          (let ([el-with-index (dp-set-element-index x-in-X.X)])
            (for*/list ([x-in-X.x (hash-keys el-with-index)]
                        [#,(if (attribute x-in-X.ind) #'x-in-X.ind #'i)
                         (list (hash-ref el-with-index x-in-X.x))]
                        #:when #,(if (attribute pred-x-ind) #'pred-x-ind #'#t))
              (let* ([x-res x-ind-expr]
                     [x-res-type (match-let-values ([(x-res-type _) (struct-info x-res)]) x-res-type)])
                (if x-res-type
                    (chaperone-struct x-res
                                      x-res-type
                                      prop:corr x-in-X.x)
                    x-res)))))]
      [(_ {x-y-indx-indy-expr (~datum for) x-in-X:element-of-a-set
                              (~datum for) y-in-Y:element-of-a-set
                              (~optional (~seq (~datum if) pred-x-y-indx-indy))})
       #`(dp-list->set
          (let ([el-with-index-Y (dp-set-element-index y-in-Y.X)])
            (apply
             append
             (for*/list ([y-in-Y.x (hash-keys el-with-index-Y)]
                         [#,(if (attribute y-in-Y.ind) #'y-in-Y.ind #'i)
                          (list (hash-ref el-with-index-Y y-in-Y.x))])
               (let ([el-with-index-X (dp-set-element-index x-in-X.X)])
                 (for*/list ([x-in-X.x (hash-keys el-with-index-X)]
                             [#,(if (attribute x-in-X.ind) #'x-in-X.ind #'j)
                              (list (hash-ref el-with-index-X x-in-X.x))]
                             #:when #,(if (attribute pred-x-y-indx-indy)
                                          #'pred-x-y-indx-indy
                                          #'#t))
                   (let* ([x-y-res x-y-indx-indy-expr]
                          [x-y-res-type (match-let-values ([(x-y-res-type _) (struct-info x-y-res)]) x-y-res-type)])
                     (if x-y-res-type
                         (chaperone-struct x-y-res
                                           x-y-res-type
                                           prop:corr x-in-X.x)
                         x-y-res))))))))]))

(define-syntax for/set
  (syntax-parser
    [(_ {elem-expr (~seq , elem-expr1) ... (~seq (~datum for) x-in-X:element-of-a-set) ...+
                   (~optional (~seq (~datum if) pred-elem))})
     ; Question: how to simplify the pred-elem part here?
     #:with (x-in-X/kc ...)
     (let ([xs (syntax->list #'(x-in-X.x ...))]
           [inds (syntax->list #'((~? x-in-X.ind #f) ...))]
           [Xs (syntax->list #'(x-in-X.X ...))])
       (for/list ([i (range 1 (+ (length Xs) 1))]
                  [an-x xs]
                  [an-ind inds]
                  [an-X Xs])
         #`[#,(if (syntax-e an-ind) #`(#,an-x #:index #,an-ind) an-x) ∈ (contracted-v/kc
            dp-set/kc #,an-X (syntax-srcloc #'#,an-X) 'for/set
            (list (format "the ~v~s set" #,i
                          '#,(ordinal-numeral i))))]))
     #`(dp-list->set
        (for/set-core ((dp-wrap-if-raw-int elem-expr)
                       (dp-wrap-if-raw-int elem-expr1) ...)
                       x-in-X/kc ...
         #,@(if (attribute pred-elem)
                #'(#:if pred-elem)
                #'(#:if))))]))


(define-syntax for/set-core
  (syntax-parser
    [(_ (elem-expr ...+) x-in-X:element-of-a-set 
                   #:if (~optional pred-expr))
     #:with (elem-res-type ...) (generate-temporaries #'(elem-expr ...))
     ; NOTE: ``dp-set-element-index'' already shrinked the set
     #`(apply
        append
        (let ([elem-with-index (dp-set-element-index x-in-X.X)])
          (for*/list ([x-in-X.x (hash-keys elem-with-index)]
                        [#,(if (attribute x-in-X.ind) #'x-in-X.ind #'i)
                         (list (hash-ref elem-with-index x-in-X.x))]
                        #:when #,(if (attribute pred-expr) #'pred-expr #'#t))
              ; TODO: Get (elem-res-type ...) for  (elem-expr ...)
              (let ([elem-res-type (match-let-values ([(elem-res-type _) (struct-info elem-expr)]) elem-res-type)]
                    ...)
                (list   
                 ; NOTE: int are now wrapped in struct.
                 ; The condition exists because we can not chaperone base types
                 ; the only base types remaining are Booleans
                 ; which does not make that sense to add as elements of set
                 (if elem-res-type
                    (chaperone-struct elem-expr ; we know it is a struct so no need to wrap int
                                      elem-res-type
                                      prop:corr x-in-X.x)
                    elem-expr)
                 ...)
                ))))]
    [(_ (elem-expr ...+) x-in-X:element-of-a-set ...+ #:if
        (~optional pred-elem))
     #:with (x0-in-X0:element-of-a-set ... xn-in-Xn:element-of-a-set) #'(x-in-X ...)
     #`(apply
        append
        (let ([el-with-index (dp-set-element-index xn-in-Xn.X)])
           (for*/list ([xn-in-Xn.x (hash-keys el-with-index)]
                       [#,(if (attribute xn-in-Xn.ind) #'xn-in-Xn.ind #'i)
                        (list (hash-ref el-with-index xn-in-Xn.x))])
             (for/set-core (elem-expr ...) x0-in-X0 ...
               #,@(if (attribute pred-elem)
                      #'(#:if pred-elem)
                      #'(#:if))))))]))

; TODO: fix the following issue:
; for [j ∈ (ints-from-to 0 i)] for [(v #:index i) ∈ Vars])
#;(define-syntax define/sets
  (syntax-parser
    [(_ (set-id0:id ...) ({el-expr0 (~seq , el-expr1) ...} ...) (~seq (~datum for) xn-in-Xn:element-of-a-set) ...+
        (~optional (~seq (~datum if) pred-expr)))
     #:with (elem-with-index0 ...) (generate-temporaries #'(xn-in-Xn ...))
     #:fail-unless (equal? (length (syntax->list #'(set-id0 ...)))
                           (length (syntax->list #'(el-expr0 ...))))
     "number of representative elements does not match the number of sets"
     #`(define-values (set-id0 ...)
         (let ([elem-with-index0 (dp-set-element-index xn-in-Xn.X)] ...)
           (for*/lists (set-id0 ... #:result (values (dp-list->set (apply append set-id0)) ...))
                       ((~@
                         [xn-in-Xn.x (hash-keys elem-with-index0)]
                         ; NOTE: ``xn-in-Xn.indx'' returns an uninterned ``i'' when ``ind'' undefined
                         [xn-in-Xn.indx (list (hash-ref elem-with-index0 xn-in-Xn.x))])
                         ...
                        #:when #,(if (attribute pred-expr) #'pred-expr #'#t))
             (values (list el-expr0 el-expr1 ...) ...))))]))

(define-syntax define/sets
  (syntax-parser
    [(_ (set-id0:id ...+) ({el-expr0 (~seq , el-expr) ...} ...+) (~seq (~datum for) xn-in-Xn:element-of-a-set) ...+
        (~optional (~seq (~datum if) pred-expr)))
     #:with (xn-in-Xn/kc ...)
     (let ([xs (syntax->list #'(xn-in-Xn.x ...))]
           [inds (syntax->list #'((~? xn-in-Xn.ind #f) ...))]
           [Xs (syntax->list #'(xn-in-Xn.X ...))])
       (for/list ([i (range 1 (+ (length Xs) 1))]
                  [an-x xs]
                  [an-ind inds]
                  [an-X Xs])
         #`[#,(if (syntax-e an-ind) #`(#,an-x #:index #,an-ind) an-x) ∈ (contracted-v/kc
            dp-set/kc #,an-X (syntax-srcloc #'#,an-X) 'for/set
            (list (format "the ~v~s set" #,i
                          '#,(ordinal-numeral i))))]))
     #'(begin
         (define set-id0
           (dp-list->set
            (for/set-core
                ((dp-wrap-if-raw-int el-expr0)
                 (dp-wrap-if-raw-int el-expr)
                 ...)
              xn-in-Xn/kc ... #:if (~? pred-expr)))) ...)]))


#;(define-syntax for/set
  (syntax-parser
    [(_ (~optional (~seq #:element-type el-type)) [x-expr (~datum for) x-in-X:element-of-a-set
                (~optional (~seq (~datum if) pred-x))])
     #`(dp-list->set
        (map
         (λ (x-in-X.x)
           (let* ([x-res #,(if (attribute el-type) #'(el-type x-expr) #'x-expr)]
                  [x-res-type (match-let-values ([(x-res-type _) (struct-info x-res)]) x-res-type)])
             (if x-res-type
                 (chaperone-struct x-res
                                   x-res-type
                                   prop:corr x-in-X.x)
                 x-res)))
         #,(if (attribute pred-x)
             #'(filter (λ (x-in-X.x) pred-x) (dp-set-members->list x-in-X.X))
             #'(dp-set-members->list x-in-X.X))))]
    [(_ (~optional (~seq #:element-type el-type)) [x-y-expr (~datum for) x-in-X:element-of-a-set (~datum for) y-in-Y:element-of-a-set
                  (~optional (~seq (~datum if) pred-x-y))])
     #`(dp-list->set
        (apply
         append ; flatten once
         (map
          (λ (y-in-Y.x)
            (map
             (λ (x-in-X.x)
               (let* ([x-y-res #,(if (attribute el-type) #'(el-type x-y-expr) #'x-y-expr)]
                      [x-y-res-type (match-let-values ([(x-y-res-type _) (struct-info x-y-res)]) x-y-res-type)])
                 (if x-y-res-type
                     (chaperone-struct x-y-res
                                   x-y-res-type
                                   prop:corr x-in-X.x)
                     x-y-res)))
             #,(if (attribute pred-x-y)
                   #'(filter (λ (x-in-X.x) pred-x-y) (dp-set-members->list x-in-X.X))
                   #'(dp-set-members->list x-in-X.X))))
          (dp-set-members->list y-in-Y.X))))]
    #;[(_ [xs-expr (~datum for) [(x:id ...) (~or in ∈) X:expr]
                 (~optional (~seq (~datum if) pred-x))])
     #''()]))

(define-syntax all-pairs-in
  (syntax-parser
    [(_ X (~optional (~and #:ordered ordered)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc X
        (syntax-srcloc #'X)
        'all-pairs-in
        (list "the value getting all pairs from"))
     #`(for/set {(tpl x y) for [(x #:index j) ∈ X/kc] for [(y #:index i) ∈ X/kc]
                            if #,(if (attribute ordered)
                                     #'(not (dp-equal? x y))
                                     #'(< (dp-int-unwrap j) (dp-int-unwrap i)))})]))

(define-syntax all-triplets-in
  (syntax-parser
    [(_ X (~optional (~and #:ordered ordered)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc X
        (syntax-srcloc #'X)
        'all-pairs-in
        (list "the value getting all triplets from"))
     #`(for/set {(tpl x y z) for [(z #:index k) ∈ X/kc] for [(x #:index j) ∈ X/kc] for [(y #:index i) ∈ X/kc]
                            if #,(if (attribute ordered)
                                     #'(and
                                        (not (dp-equal? x y))
                                        (not (dp-equal? y z))
                                        (not (dp-equal? x y)))
                                     #'(and
                                        (< (dp-int-unwrap j) (dp-int-unwrap i))
                                        (< (dp-int-unwrap k) (dp-int-unwrap j))))})]))


(define-syntax find-one
  (syntax-parser
    [(_ x-in-X:element-of-a-set (~optional (~seq (~datum s.t.) pred-x?)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'find-one
        (list "the value to search from"))
     #`(let ([res (r:findf (r:λ (x-in-X.x)
                               (r:and
                                (set-∈ x-in-X.x X/kc)
                                #,(if (attribute pred-x?) #'pred-x? #t)))
                           (dp-ground-set->list X/kc))])
         ; XXX: the result will be incorrect when finding the boolean value #f
         (contracted-v/kc
          (make-simple-contract/kc (v)
            v
            "can not find such an element")
          res (syntax-srcloc #'x-in-X.X) 'find-one (list "the set to search from")))]))

(define-syntax argmax
  (syntax-parser
    [(_ x-expr x-in-X:element-of-a-set (~optional (~seq (~datum s.t.) pred-x?)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'argmax
        (list "the value to taken argmax from"))
     #`(let ([set-member-lst
              (dp-set-members->list
               (for/set {(tuple x-expr x-in-X.x) for [x-in-X.x in X/kc] if (~? pred-x? #t)}))])
         (snd
          (lst-argmax
           (λ (x-in-X.x) (dp-int-unwrap
                          (contracted-v/kc
                             (dp-integer-w/kc #f)
                             (fst x-in-X.x)
                             'argmax
                             (syntax-srcloc #'x-expr)
                             (list "an value to be considered maximum"))))
           set-member-lst)))]))

(define-syntax arg-kth-max
  (syntax-parser
    [(_ k x-expr x-in-X:element-of-a-set (~optional (~seq (~datum s.t.) pred-x?)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'arg-kth-max
        (list "the value to taken k-th max from"))
     #:with k/kc
     #`(contracted-v/kc
        (and/kc (dp-natural-w/kc #f) dp-int-not-exp-size/kc)
        k (syntax-srcloc #'k) 'arg-kth-max
        (list "the index k"))
     #`(let rec ([n (dp-int-unwrap k/kc)]
                 [max-xs (set )])
         (let ([cur-max
                (argmax (contracted-v/kc
                             (dp-integer-w/kc #f)
                             x-expr
                             'arg-kth-max
                             (syntax-srcloc #'x-expr)
                             (list "an value to be considered k-th maximum"))
                        [x-in-X.x in (set-minus X/kc max-xs)]
                        (~? (~@ s.t. pred-x?)))])
           (if (<= n 1)
               cur-max
               (rec (- n 1)
                 (set-∪ max-xs (set cur-max))))))]))

(define-syntax argmin
  (syntax-parser
    [(_ x-expr x-in-X:element-of-a-set (~optional (~seq (~datum s.t.) pred-x?)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'argmin
        (list "the value to taken argmin from"))
     #:with x-expr/kc
     #`(contracted-v/kc
        (dp-integer-w/kc #f) x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'argmin
        (list "the value to taken argmin from"))
     #`(let ([set-member-lst
              (dp-set-members->list
               (for/set {(tuple x-expr x-in-X.x) for [x-in-X.x in X/kc] if (~? pred-x? #t)}))])
         (snd
          (lst-argmin
           (λ (x-in-X.x) (dp-int-unwrap
                          (contracted-v/kc
                           (dp-integer-w/kc #f)
                           (fst x-in-X.x)
                           'arg-min
                           (syntax-srcloc #'x-expr)
                           (list "an value to be considered minimum"))))
           set-member-lst)))]))

(define-syntax arg-kth-min
  (syntax-parser
    [(_ k x-expr x-in-X:element-of-a-set (~optional (~seq (~datum s.t.) pred-x?)))
     #:with X/kc
     #`(contracted-v/kc
        dp-set/kc x-in-X.X
        (syntax-srcloc #'x-in-X.X)
        'arg-kth-max
        (list "the value to taken k-th min from"))
     #:with k/kc
     #`(contracted-v/kc
        (and/kc (dp-natural-w/kc #f) dp-int-not-exp-size/kc)
        k (syntax-srcloc #'k) 'arg-k-min
        (list "the index k"))
     #`(let rec ([n (dp-int-unwrap k/kc)]
                 [min-xs (set )])
         (let ([cur-min
                (argmin (contracted-v/kc
                             (dp-integer-w/kc #f)
                             x-expr
                             'arg-kth-min
                             (syntax-srcloc #'x-expr)
                             (list "an value to be considered k-th minimum"))
                        [x-in-X.x in (set-minus X/kc min-xs)]
                        (~? (~@ s.t. pred-x?)))])
           (if (<= n 1)
               cur-min
               (rec (- n 1)
                 (set-∪ min-xs (set cur-min))))))]))

; Begin -- old version
#;(define-syntax foreach/set  
  (syntax-parser
    #:datum-literals (in)
    [(_ ([x in X] ...) body)
     #'(make-immutable-hash
        (map
         (λ (e) (cons e #t))
         (filter
          identity
          (apply append ; flatten once
              (for/list ([x X] ...)
                body)))))
     ]))

#;(define-syntax find-one
  (syntax-parser
    #:datum-literals (in as s.t.)
    [(_ [x:id in X] (~optional (~seq as as-body)) s.t. pred?)
     (if (attribute as-body)
         ; return singleton list
         #'(list (r:let ([the-one (r:findf (r:λ (x) pred?) X)])
                  (r:if the-one
                        (r:λ (x) as-body)
                        the-one)) )
         #'(list (r:findf (r:λ (x) pred?) X)))]))

; not in use, use for/set instead
(define-syntax find-all
  (syntax-parser
    #:datum-literals (in as s.t.)
    [(_ [x:id in X] (~optional (~seq as as-body)) s.t. pred?)
     #:with filtered #'(r:filter (r:λ (x) pred?) X)
     ; FIXME: not unified with find-one
     (if (attribute as-body)
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             (r:let ([alls filtered])
                  (r:map
                   (r:λ (x) as-body)
                   alls))
         
         ))
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             filtered

             ))
         )]
    [(_ [(x:id ...) in X] (~optional (~seq as as-body)) s.t. pred?)
     #:with filtered #'(r:filter
                        (r:λ
                         (a-lst)
                         (match-let ([(list x ...) a-lst])
                           pred?))
                        X)
     (if (attribute as-body)
         #'(make-immutable-hash
        (map
         (λ (e) (cons e #t))

         (r:let ([alls
                    filtered])
                  (r:map
                   (r:λ (a-lst)
                        (match-let ([(list x ...) a-lst])
                          as-body))
                   alls))
         
         ))
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             filtered

             ))
         )]))

#;(define (all-pairs-in X)
  (cond [(hash? X) (combinations
                    (filter (λ (x)
                              (hash-ref X x))
                            (hash-keys X)) 2)]
        [(list? X) (combinations X 2)]))

; range constructors
(define/contract/kc (ints-from-to from to)
  (->k ([from any/kc]
        [to (and/kc
            (dp-natural-w/kc #f)
            #;(make-simple-contract (v)
              (dp-int-ge v 1)
              "index needs to be at least 1")
            dp-int-not-exp-size/kc)])
       any/kc)
  (dp-list->set
   (map
    (λ (a-raw-int) (dp-int-wrap a-raw-int (dp-int-size-of to)))
    (range from (+ (dp-int-unwrap to) 1)))))


;; macro
(provide
 define-forward-instance-construction
 target-inst
 define-forward-certificate-construction
 define-backward-certificate-construction)

(define-syntax (define-forward-instance-construction stx)
  (syntax-parse stx
    [(_ (~seq #:from s)
        (~seq #:to t)
        (proc-id:id inst-id:id)
        body* ...+)
     (with-syntax (;[s->t-construction (format-id #'s "~a->~a" #'s #'t)]
                   [a-s-instance (format-id #'s "a-~a-instance" #'s)]
                   #;[s->t-construction/c
                      (format-id #'s "~a->~a-construction/c" #'s #'t)]
                   [instance-type-info (format-id #'t "dp-instance-type-~a" #'t)]
                   [instance-type-annotate (format-id #'s "dp-annotate-instance-type-~a" #'s)]
                   [proc-id-internal (generate-temporary #'proc-id)])      
       #'(begin

           (define (proc-id-internal a-s-instance)
             ; add type annotation to source instance argument
             (define-syntax inst-id
               (instance-type-annotate #'a-s-instance))
           
             body* ...)
           
           (define-syntax proc-id
             (func-type-info
              (syntax-local-value #'instance-type-info)
              (syntax-parser
                [(_ arg0 (... ...))
                 #'(proc-id-internal arg0 (... ...))]
                [_:id #'proc-id-internal])))
           )
       )]))

(define-syntax-parameter target-inst
  (lambda (stx)
    (raise-syntax-error #f "can not be used outside certificate constructions" stx)))

(define-syntax (define-forward-certificate-construction stx)
  (syntax-parse stx
    [(_ (~seq #:from s)
        (~seq #:to t)
        (proc-id:id s->t-construction:id inst-id:id a-s-cert:id)
        body* ...+)
     (with-syntax (#;[s->t-cert-construction
                      (format-id #'s "~a->~a-certificate-construction" #'s #'t)]
                   [a-s-instance (format-id #'s "a-~a-instance" #'s)]
                   ;[a-s-cert (format-id #'s "a-~a-certificate" #'s)]
                   ;[s->t-construction (format-id #'s "~a->~a" #'s #'t)]
                   #;[s->t-cert-construction/c
                      (format-id #'s "~a->~a-certificate-construction/c" #'s #'t)]
                   [s-instance-type-annotate (format-id #'s "dp-annotate-instance-type-~a" #'s)]
                   [t-instance-type-annotate (format-id #'t "dp-annotate-instance-type-~a" #'t)]
                   [t-inst-id (format-id #'t "target-inst")])
       
         #'(define (proc-id
                    s->t-construction
                    a-s-instance
                    a-s-cert)
           
             ; add type annotation to source instance argument
             (define-syntax inst-id
               (s-instance-type-annotate #'a-s-instance))
             ; add type annotation to target instance if present
             (define t-inst-runtime (s->t-construction a-s-instance))

             ; Question: How to make this work with syntax-parameterize
             (define-syntax t-inst-id (t-instance-type-annotate #'t-inst-runtime))
             
         body* ...)
       )
     ]))

(define-syntax (define-backward-certificate-construction stx)
  (syntax-parse stx
    [(_ (~seq #:from s)
        (~seq #:to t)
        (proc-id:id s->t-construction:id inst-id:id a-t-cert:id)
        body* ...+)
     (with-syntax (#;[t->s-cert-construction
                      (format-id #'s "~a->~a-certificate-construction" #'t #'s)]
                   [a-s-instance (format-id #'s "a-~a-instance" #'s)]
                   ;[a-t-cert (format-id #'s "a-~a-certificate" #'t)]
                   ;[s->t-construction (format-id #'s "~a->~a" #'s #'t)]
                   #;[t->s-cert-construction/c
                      (format-id #'s "~a->~a-certificate-construction/c" #'t #'s)]
                   [s-instance-type-annotate (format-id #'s "dp-annotate-instance-type-~a" #'s)]
                   [t-instance-type-annotate (format-id #'t "dp-annotate-instance-type-~a" #'t)]
                   [t-inst-id (format-id #'t "target-inst")]
                   [proc-id-for-checking (format-id #'s "~a/checking" #'proc-id)])
       
       #`(define (proc-id
                  s->t-construction
                  a-s-instance
                  a-t-cert)
           
           ; add type annotation to source instance argument
           (define-syntax inst-id
             (s-instance-type-annotate #'a-s-instance))
           ; add type annotation to target instance if present
           (define t-inst-runtime (s->t-construction a-s-instance))

           ; Question: How to make this work with syntax-parameterize
             (define-syntax t-inst-id (t-instance-type-annotate #'t-inst-runtime))
           
           body* ...)
       )
     ]))

; check reduction correctness
(define-syntax (check-reduction stx)
  (syntax-parse stx
    [(_ (~seq #:from s)
        (~seq #:to t)
        (~optional (~seq #:from-generator (src-gen ...+)))
        (~optional (~seq #:n-test n-test))
        (~optional (~seq #:continue-after-failure cont-after-fail))
        (~optional (~seq #:random-seed seed))
        s->t-construction:id
        s->t-cert-construction:id
        t->s-cert-construction:id)
     #:with num-tests (if (attribute n-test) #'n-test #'10)
     #:with cont-after-fail? (if (attribute cont-after-fail) #'cont-after-fail #'#f)
     #:with set-seed-stmt (if (attribute seed) #'(when seed (random-seed seed)) #'(begin ))
     (with-syntax ([s-instance/kc (format-id #'s "~a-instance/kc" #'s)]
                   [t-instance/kc (format-id #'t "~a-instance/kc" #'t)]
                   [yes-s/kc (format-id #'s "yes-~a/kc" #'s)]
                   [no-s/kc (format-id #'s "no-~a/kc" #'s)]
                   [yes-t/kc (format-id #'t "yes-~a/kc" #'t)]
                   [no-t/kc (format-id #'t "no-~a/kc" #'t)]
                   [s-certificate/kc (format-id #'s "~a-certificate/kc" #'s)]
                   [t-certificate/kc (format-id #'t "~a-certificate/kc" #'t)]
                   [s-solver (format-id #'s "~a-solver" #'s)]
                   [t-solver (format-id #'t "~a-solver" #'t)]
                   [s-cert-checker (format-id #'s "~a-verifier" #'s)]
                   [t-cert-checker (format-id #'t "~a-verifier" #'t)]
                   [s-null-cert (format-id #'s "null-~a-cert" #'s)]
                   [t-null-cert (format-id #'t "null-~a-cert" #'t)]
                   [s-inst-pretty-printer (format-id #'s "pretty-print-~a-instance" #'s)]
                   [t-inst-pretty-printer (format-id #'t "pretty-print-~a-instance" #'t)]
                   [s-gen (if (attribute src-gen)
                              #'(λ () src-gen ...)
                              (format-id #'s "generate-~a-instance" #'s))]
                   [found-counterexample? (format-id #'s "found-counterexample?")]
                   [get-counterexample (format-id #'s "get-counterexample")]
                   [counterexample-id-internal (generate-temporary #'get-counterexample)]
                   [instance-type-info (format-id #'s "dp-instance-type-~a" #'s)])
       #'(begin
           (define
             counterexample-id-internal
             (call/cc
              (λ (return)
                (displayln "Testing Reduction...")
                set-seed-stmt
                (for ([i (range num-tests)])
                  (begin
                    (displayln "----------------------------------------")
                    (display "Test ")
                    (display (number->string i))
                    (displayln ":")
                    (displayln "Testing forward instance construction...")
                    (let* ([a-s-inst (s-gen)]
                           [a-s-cert (s-solver a-s-inst)]
                           [the-t-inst (s->t-construction a-s-inst)])
                      ; check if s->t-constr yields a t-instance
                      (unless ((make-predicate/kc t-instance/kc) the-t-inst)
                        (displayln "Test failed: result not a to-problem instance")
                        (displayln "From-problem instance:")
                        (s-inst-pretty-printer a-s-inst)
                        (displayln "Produced:")
                        (pretty-print the-t-inst)
                        (unless cont-after-fail?
                          (return a-s-inst)))
                      ; check yes ~~> yes and no ~~> no
                      (define a-t-cert (t-solver the-t-inst))
                      ; when source is no
                      (when (dp-equal? a-s-cert s-null-cert)
                        ; check if target is also no
                        (unless (dp-equal? a-t-cert t-null-cert)
                          (displayln "Test failed: no-instance mapped to a yes-instance")
                          (displayln "From-problem instance:")
                          (s-inst-pretty-printer a-s-inst)
                          (displayln "To-problem instance:")
                          (t-inst-pretty-printer the-t-inst)
                          (displayln "To-instance certificate:")
                          (pretty-print a-t-cert)
                          (unless cont-after-fail?
                            (return a-s-inst))))
                      ; when target is no
                      (when (dp-equal? a-t-cert t-null-cert)
                        ; check if source is also no
                        (unless (dp-equal? a-s-cert s-null-cert)
                          (begin
                            (displayln "Test failed: yes-instance mapped to a no-instance")
                            (displayln "From-problem instance:")
                            (s-inst-pretty-printer a-s-inst)
                            (displayln "From-instance certificate:")
                            (pretty-print a-s-cert)  
                            (displayln "To-problem instance:")
                            (t-inst-pretty-printer the-t-inst)                  
                            (unless cont-after-fail?
                              (return a-s-inst)))))
                      (unless (or (equal? a-s-cert s-null-cert)
                                  (equal? a-t-cert t-null-cert))
                        (displayln "Testing forward certificate construction...")
                        (define the-t-cert (s->t-cert-construction
                                            s->t-construction
                                            a-s-inst
                                            a-s-cert))
                        ; check forward-certificate-construction                   
                        (unless (and
                                 ((make-predicate/kc (t-certificate/kc the-t-inst)) the-t-cert)
                                 (t-cert-checker the-t-inst the-t-cert))
                          (displayln "Test failed: result not a certificate of the to-problem instance")
                          (displayln "From-problem instance:")
                          (s-inst-pretty-printer a-s-inst)
                          (displayln "Produced to-problem instance:")
                          (t-inst-pretty-printer the-t-inst)
                          (displayln "From-instance certificate:")
                          (pretty-print a-s-cert)                      
                          (displayln "Produced to-instance certficate:")
                          (pretty-print the-t-cert)      
                          (unless cont-after-fail?
                            (return a-s-inst)))
                        (displayln "Testing backward certificate construction...")
                        (define the-s-cert (t->s-cert-construction
                                            s->t-construction
                                            a-s-inst
                                            a-t-cert))
                        ; check backward-certificate-construction                
                        (unless (and
                                 ((make-predicate/kc (s-certificate/kc a-s-inst)) the-s-cert)
                                 (s-cert-checker a-s-inst the-s-cert))
                          (displayln "Test failed: result not a certificate of the from-problem instance")
                          (displayln "From-problem instance:")
                          (s-inst-pretty-printer a-s-inst)
                          (displayln "Produced to-problem instance:")
                          (t-inst-pretty-printer the-t-inst)  
                          (displayln "To-instance certificate:")
                          (pretty-print a-t-cert)
                          (displayln "Produced from-instance certificate:")
                          (pretty-print the-s-cert)      
                          (unless cont-after-fail?
                            (return a-s-inst)))
                        ))
                    (displayln "Finished!")))
                'no-counterexample-found)))

           (define (found-counterexample?)
             (not (equal? counterexample-id-internal 'no-counterexample-found)))

           (define-syntax get-counterexample
             (func-type-info
              (syntax-local-value #'instance-type-info)
              (syntax-parser
                [(_)
                 #'((λ ()
                      (if (found-counterexample?)
                          counterexample-id-internal
                          (error "No counterexample found"))))]))))
       
       #;(for/fold ([pass #t]
                  [s-inst null])
                 ([i (range num-tests)])
         #:break (not pass)
         (let* ([a-s-inst (src-gen)]
                [the-t-inst (s->t-construction a-s-inst)])
           
           (values pass a-s-inst))))]))

(define-syntax (export-test stx)
  (syntax-parse stx
    [(_ name (body ...+))
     #`(begin
         (define (name) body ... #f)
         (provide name))]))

(define-syntax (export-test-incorrect stx)
  (syntax-parse stx
    [(_ name (body ...+))
     #:with found-counterexample? (format-id #'name "found-counterexample?")
     #`(begin
         (define (name)
           (let/ec exit
              (let loop ()
                (with-handlers ([exn:fail? (λ (e) (exit))])
                  body ...
                  (if (found-counterexample?) (exit) (loop)))))
           #f)
         (provide name))]))

; utility for random generator
(provide random-natural-numeric
         random-natural-cardinal)

(define (random-natural-numeric a b)
  (gen-random-natural a b 'exp))

(define (random-natural-cardinal a b)
  (gen-random-natural a b 'poly))