#lang racket

(require [except-in "../reduction-base.rkt" define]
         [rename-in "mapping.rkt" [mapping m-mapping] ]
         [for-syntax syntax/parse
                     syntax/stx]
         racket/stxparam)


(provide mapping
         defined?
         (all-from-out "mapping.rkt"))

; mapping constructor
#;(define-syntax mapping
  (syntax-parser
    #;[(_ #:from dom [(~or x:id (x:id #:index ind:id)) (~datum ~>) x-expr])
     #`(let ([elem-with-index (dp-set-element-index dom)])
         (dp-mapping
          (for*/hash ([x (hash-keys elem-with-index)]
                      [#,(if (attribute ind) #'ind #'i)
                       (hash-ref elem-with-index x)])
            (values x x-expr))))]
    [(_ [x (~or (~datum in) (~datum ∈)) X] (~optional (~seq (~datum where) pred-x)) (~datum ~>) x-expr)
     #`(let ([elem-with-index (dp-set-element-index X)])
         (let-values ([(H defined)
                       (for*/fold ([curr-H (hash)] ; 
                                   [defined (for/hash ([k (hash-keys elem-with-index)]) (values k #f))])
                                  ([x (hash-keys elem-with-index)]
                                   ; Question: we actually want a ``let'', simpler way?
                                   [curr-M (list (dp-mapping curr-H defined))]
                                   #:when (~?
                                           (syntax-parameterize
                                              ([curr (make-rename-transformer #'curr-M)])
                                             pred-x)
                                           #t))
                         (values (syntax-parameterize ([curr (make-rename-transformer #'curr-M)])
                                   (hash-set curr-H x x-expr))
                                 (hash-set defined x #t)))])
           (dp-mapping
            H
            #,(if (attribute pred-x)
                  #'defined
                  #'#f)))
         )]
    [(_ sth ...) #'(m-mapping sth ...)]))

(define (defined? a-mapping k)
  (hash-ref (dp-mapping-defined a-mapping) k #f))

(define-syntax build-mapping-core
  (syntax-parser
    [(_ curr-H curr-defined (x0:id X0 (~optional pred-x0) x-expr0) (x:id X (~optional pred-x) x-expr) ...)
     #:with rest-xs #'(x ...)
     #`(let-values
           ([(res-H res-defined)
             (let ([elem-with-index (dp-set-element-index X0)])
               (for*/fold ([H curr-H] ; 
                           [defined curr-defined])
                          ([x0 (hash-keys elem-with-index)]
                           ; Question: we actually want a ``let'', simpler way?
                           [curr-M (list (dp-mapping H #f defined))] ; intemmediate result, el-rep not set
                           #:when (~?
                                   (syntax-parameterize
                                       ([curr (make-rename-transformer #'curr-M)])
                                     pred-x0)
                                   #t))
                 (values (syntax-parameterize ([curr (make-rename-transformer #'curr-M)])
                           (hash-set H x0 x-expr0))
                         (hash-set defined x0 #t))))])
         #,(if (equal? (length (stx->list #'rest-xs)) 0)
               #'(dp-mapping
                  res-H
                  (if (dp-mergeable? (car (hash-values res-H)))
                      (gen-representative-el-from-lst (hash-values res-H) (car (hash-values res-H)))
                      #f)
                  ; clear the temporary state for whether a key is defined
                  #f)
               #'(build-mapping-core res-H res-defined (x X (~? pred-x) x-expr) ...)))]))
;
; For elements appears in multiple sets, later will override the former
; See mapping-reduction-test.rkt for examples
(define-syntax mapping
  (syntax-parser
    [(_ (~seq [x (~or (~datum in) (~datum ∈)) X] (~optional (~seq (~datum where) pred-x)) (~datum ~>) x-expr) ...+)
     #`(build-mapping-core
        (hash) ; init curr-H to empty hash 
        (for/hash ([k (dp-set-members->list (set-∪ X ...))]) (values k #f)) ; init curr-defined to indicate nothing is defined
        (x X (~? pred-x) x-expr) ...)]
    [(_ sth ...) #'(m-mapping sth ...)]))

; simple testing
#;(mapping [x ∈ (set 0 1 2 3 4 5)] where (and (> x 0)
                                            (not (defined? curr (- x 1))))
           ~> (* 2 x))