#lang racket

(require
  racket/generic
  [for-syntax syntax/parse
              racket/struct
              racket/syntax
              syntax/stx
              racket/list
              racket/match]
  [for-meta 2 racket/base
              syntax/parse]
  [prefix-in r: rosette/safe])

(provide
  ; type-interface 
 (for-syntax
  prop:type-interface
  interfaced-type?
  get-type-interface)
 ; (simple) function type annotate
 ; without compilation conditional on types
 kv-func-type-annotate)

(begin-for-syntax
  ; generic interface for types, wider than interface for objects
  (define-values (prop:type-interface interfaced-type? get-type-interface)
    (r:make-struct-type-property 'type-interface))

  ; implementation details subject to change
  (provide make-τ get-tag get-τb args-τ)

  (define-match-expander args-τ
    (syntax-parser [(_ (tag τb) ...) #'(list (cons tag τb) ...)]))
  (define (make-τ tag τb) (cons tag τb))
  (define (get-tag a-tagged-kv-type)
    (car a-tagged-kv-type))
  (define (get-τb a-tagged-kv-type) ; returns a kv-type-object
      (cdr a-tagged-kv-type))

)


; type object representing type variable
; can only be used in annotation
(begin-for-syntax
  (provide α-τb)
  
  (struct ty-α ())

  (define-syntax α-τb
    (λ (stx) #'(ty-α)))
)



(define-syntax kv-func-type-annotate
  (syntax-parser
    [(_ func-id:id (τb-arg ... τb-out) (~optional expects))
     #:with arg-τbs-stx #'(τb-arg ...)
     #:with rewriter-id (format-id #'func "~a-typed-rewriter" #'func-id)
     (let ([arg-τb-lst (stx->list #'arg-τbs-stx)])
     #`(begin
         (provide rewriter-id)
         (define-syntax rewriter-id
         (λ (type-lst)
           (if (not (equal? #,(length arg-τb-lst)
                            (length type-lst)))
               (syntax-parser
                 [(func arg (... ...))
                  (raise-syntax-error #f
                                      (format "expects ~a arguments, gets ~a"
                                              #,(length arg-τb-lst)
                                              (length type-lst))
                                          #'(func arg (... ...))
                                          #'func)])
               (begin
                 ;(raise-syntax-error #f (map get-τb type-lst))
                 (match (map get-τb type-lst)
                   [(list τb-arg ...)
                    (λ (stx) (cons stx τb-out))]
                   #,@(for/list ([i (range (- (length arg-τb-lst) 1) -1 -1)])
                        #`[(list #,@(take arg-τb-lst i) τb-mismatch _ (... ...))
                           ;(let ([τb-expected #,(list-ref arg-τb-lst i)])
                             (λ (stx)
                               (syntax-parse stx
                                 [(#,@(make-list (+ i 1) #'_) stx-mismatch _ (... ...))
                                  (raise-syntax-error
                                   #f
                                   (format "type mismatch:~a gets ~a"
                                           #,(if (attribute expects)
                                                 (string-append " expects "
                                                                (syntax->datum #'expects)
                                                                ",")
                                                 "")
                                           (map get-τb type-lst))
                                   #;(format "expects type ~v, gets ~v"
                                             #,(list-ref arg-τb-lst (+ i 1))
                                             τb-mismatch)
                                   stx
                                   #'stx-mismatch)
                                  ]));)
                             ]))))))))
     ]))