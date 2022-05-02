#lang racket

(require [for-syntax racket/syntax
                     syntax/parse])


(begin-for-syntax
  (provide (struct-out type-info)
           (struct-out func-type-info))

  ; type-info struct for static information
  (struct type-info
    (name   ; type-name
     idxes  ; indices of field: symbol? -> natural?
     runtime-id ; underlying runtime-id
     )
    #:property prop:procedure
    (λ (self stx)
      ; transforms to runtime-id
      (type-info-runtime-id self))
    #:transparent)

  (struct func-type-info
    (ret-type ; type-info of return structure
     func
     )
    #:property prop:procedure
    ; redirect the expansion to the ``procedure'' field
    (struct-field-index func)))

; custom define

(provide dp-define)


; custom define
; restricting to defining variables, i.e. no function definition
; XXX: some issue not completely resolved
(define-syntax (dp-define stx)
  (syntax-parse stx
    [(_ x:id (f arg ...))
     (let ([the-func-type-info
            ; get the annotation on the function part
            (syntax-local-value
             #'f
             (λ () #f) ; returns #f if no type information
             )])
       (if (and (func-type-info? the-func-type-info)
                (type-info? (func-type-info-ret-type the-func-type-info)))
           (with-syntax ([runtime-id (generate-temporary #'f)]
                         ; not in use, see below
                         #;[type-info-3d-stx (func-type-info-ret-type the-func-type-info)])
             #`(begin
                 (define runtime-id (f arg ...))
                 (define-syntax x
                   ;
                   ; Refer to the definition of ``create-instance'' in decision-problem
                   ;
                   ; the following gives out error that
                   ; "given value instantiates a different structure type with the same name"
                   ; see the ``type-info-3d-stx'' defined above 
                   ;------------
                   #;(type-info
                    (type-info-name type-info-3d-stx)
                    (type-info-idxes type-info-3d-stx)
                    #'runtime-id)
                   ;-------------
                   
                   ; the following works but not very elegant
                   ;-------------
                   (type-info
                    '#,(type-info-name (func-type-info-ret-type the-func-type-info))
                    #,(type-info-idxes (func-type-info-ret-type the-func-type-info))
                    #'runtime-id)
                   ;-------------

                   ; the following gives out error that
                   ; expecting ``type-info?''
                   ; but the value of
                   ; ```#,(func-type-info-ret-type the-func-type-info)'''
                   ; is not.
                   ; likely to be the same problem as the first case
                   ;-------------
                   #;(struct-copy
                      type-info
                      #,(func-type-info-ret-type the-func-type-info)
                      [#,(quote-syntax runtime-id) #'runtime-id])
                   ;--------------
                   )))
           #'(define x (f arg ...))))]
    [(_ x:id def:id)
     (let ([the-type-info
            (syntax-local-value
             #'def
             (λ ()
               #f))])
       (if (type-info? the-type-info)
           ; simply renaming
           #`(define-syntax x
               #,the-type-info)
           #'(define x def)))]
    [(_ x:id def)
     #'(define x def)]))