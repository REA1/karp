#lang racket

(require
  racket/stxparam
  racket/splicing
  [for-syntax syntax/parse]
  [for-meta 2 racket/base
              racket/list
              syntax/parse])

(provide
 (for-syntax dp-stx-info
             dp-stx-info-field
             dp-stx-type-info
             dp-stx-type-desc
             dp-stx-type-info-field
             dp-stx-type-desc-field
             dp-stx-type-info-accessor-ref
             dp-stx-type-desc-accessor-ref
             dp-stx-type-info-data-ref
             dp-stx-type-desc-data-ref))

; type-info : describes the type of this value
; type-desc : the type that the descriptor describes

; following syntax-property
(begin-for-syntax

  ; why this does not work
  #;(define-syntax dp-type-info
    (syntax-parser
      [(_ (~seq key:id value) ...+)
       #:with ks #'(key ...)
       #:with vs #'(value ...)
       #`(make-immutable-hash
          '#,(for*/list
                 ([k (syntax->list #'ks)]
                  [v (syntax->list #'vs)])
               (cons (syntax->datum k) v)))]))

  ; like hash but use id as key name directly
  (define-syntax dp-stx-info
    (syntax-parser
      [(_  (~seq key:id value) ...+)
       #:with kvs #'((key value) ...)
       #`(hash
           #,@(flatten
               (map
                (λ (x)
                  (cons #`'#,(syntax->datum
                              (car (syntax->list x)))
                        (cdr (syntax->list x))))
                (syntax->list #'kvs))))]))
  
  (define-syntax dp-stx-info-field
    (syntax-parser
      [(_ x:expr field:id
          (~optional undef-ret #:defaults ([undef-ret #''undefined])))
       #`(if
          x
          (hash-ref x '#,(syntax->datum #'field) undef-ret)
          undef-ret)]))

  #;(define-syntax dp-stx-type-info
    (syntax-parser
      [(_ base-stx (~seq key:id value) ...+)
       #:with kvs #'((key value) ...)
       #`(syntax-property
          base-stx
          'type-info
          (hash
           #,@(flatten
               (map
                (λ (x) (cons #`'#,(syntax->datum
                                 (car (syntax->list x)))
                             (cdr (syntax->list x))))
                (syntax->list #'kvs)))))]))

  ; usage
  ; create stx-obj w/ field (dp-stx-type-info stx k0 v0 k1 v1 ...)
  ; get type-info (dp-stx-type-info stx)
  (define-syntax dp-stx-type-info
    (syntax-parser
      ; literal copy everything
      [(_ base-stx info-entry)
       #`(syntax-property
          base-stx
          'type-info
          info-entry)]
      ; key-value pairs
      [(_ base-stx rest0 rest1 ...+)
       #:with passover #'(rest0 rest1 ...)
       #`(syntax-property
          base-stx
          'type-info
          (dp-stx-info rest0 rest1 ...))]
      [(_ base-stx)
       ; why does not work
       #;#`(syntax-property
            #'base-stx
            'type-info)
       #`(syntax-property
          base-stx
          'type-info)]))

  (define-syntax dp-stx-type-desc
    (syntax-parser
      ; literal copy everything
      [(_ base-stx desc-entry)
       #`(syntax-property
          base-stx
          'type-desc
          info-entry)]
      ; key-value pairs
      [(_ base-stx rest0 rest1 ...+)
       #:with passover #'(rest0 rest1 ...)
       #`(syntax-property
          base-stx   ; the ``base-stx'' part will not expand if #'base-stx is used instead
          'type-desc
          (dp-stx-info rest0 rest1 ...))]
      [(_ base-stx)
       #'(let ([type-desc
                (syntax-property
                 base-stx
                 'type-desc)])
           (if type-desc
               type-desc
               (raise-syntax-error #f "invalid type descriptor" base-stx)))]))
  
  (define-syntax dp-stx-type-info-field
    (syntax-parser
       [(_ x field:id)
        #'(dp-stx-info-field
           (syntax-property
            x
            'type-info)
           field)]
       [(_ x field:id undef-ret)
        #'(dp-stx-info-field
           (syntax-property
            x
            'type-info)
           field
           undef-ret)]))

    (define-syntax dp-stx-type-desc-field
      (syntax-parser
        [(_ x field:id)
         #'(dp-stx-info-field
            (syntax-property
             x
             'type-desc)
            field)]
        [(_ x field:id undef-ret)
        #'(dp-stx-info-field
           (syntax-property
            x
            'type-desc)
           field
           undef-ret)]))

    #;(define-syntax dp-stx-type-info-accessor-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-info-field
             x
             accessors))]))

    (define (dp-stx-type-info-accessor-ref x key)
      (let ([the-assoc
             (dp-stx-type-info-field
              x
              accessors
              #f)])
        (if the-assoc
            (let ([v (assoc
                      key
                      the-assoc)])
              (if v
                  (cdr v)
                  'undefined))
            'undefined)))
    
    #;(define-syntax dp-stx-type-desc-accessor-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-desc-field
             x
             accessors))]))

    (define (dp-stx-type-desc-accessor-ref x key)
      (let ([the-assoc
             (dp-stx-type-desc-field
              x
              accessors
              #f)])
        (if the-assoc
            (let ([v (assoc
                      key
                      the-assoc)])
              (if v
                  (cdr v)
                  'undefined))
            'undefined)))

    #;(define-syntax dp-stx-type-info-data-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-info-field
             x
             type-data))]))


    (define (dp-stx-type-info-data-ref x key)
      (let ([the-assoc
             (dp-stx-type-info-field
              x
              type-data
              #f)])
        (if the-assoc
            (let ([v (assoc
                      key
                      the-assoc)])
              (if v
                  (cdr v)
                  'undefined))
            'undefined)))

    #;(define-syntax dp-stx-type-desc-data-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-desc-field
             x
             type-data))]))

    (define (dp-stx-type-desc-data-ref x key)
      (let ([the-assoc
             (dp-stx-type-desc-field
              x
              type-data
              #f)])
        (if the-assoc
            (let ([v (assoc
                      key
                      the-assoc)])
              (if v
                  (cdr v)
                  'undefined))
            'undefined)))

)


#;(define-syntax test-type
  (syntax-parser
    [(_ k:id v) (dp-stx-type-info #'2 k (+ 1 2) gt (string-append "abc" "def"))]))

#;(define-syntax test-inspector
  (syntax-parser
    [(_ t k:id)
     #`#,(dp-stx-type-info-field
          (local-expand #'t 'expression #f) gt)]))

#;(test-inspector (test-type a 1) a)

#;(pretty-print
 (dp-type-info-field
  (dp-type-info a 1 b 2) c))