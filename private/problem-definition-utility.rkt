#lang racket

(require "dp-stx-info.rkt"
         "dp-type-info.rkt"
         racket/stxparam
         racket/generic
         [for-syntax racket/list
                     syntax/stx
                     syntax/id-table]
         (prefix-in r: rosette))
;
; Problem definition
;
(provide

 [all-from-out "dp-stx-info.rkt"
               "dp-type-info.rkt"]
 ; solver environment marking
 dp-solver-env?

 ; problem definition parsing related
 (struct-out dp-instance)
 [for-syntax dp-parse-table
             dp-part-cert-env?
             dp-cur-field-id
             ;assert-parse-table-ref             
             parsed-entry-type
             parsed-entry-idx
             get-field-from-parsed
             get-field-index-from-parsed
             parsed-table-with-temp-field
             instance-field-ref
             get-size-as-num
             trace-upstream-to-field
             dp-expand-part
             dp-expand-parts

             unsupport-in-certificate-msg
             unsupport-outside-problem-definition-msg

             ]
 v-dep-any/c

 prop:interface
 interfaced-struct?
 get-interface

 ; structural constraint
 prop:struct-constr
 has-struct-constr?
 struct-constr

 r-symbolic-atom?
 dp-symbolic?
 )

; dp-solver-env? => current checker is used body is to send to the solver
; example usage: in graph connectivity, solver env needs to add additional
; auxiliary vairables
(define-syntax-parameter dp-solver-env? #f)

(define-for-syntax unsupport-in-certificate-msg "can not be used in certificate")
(define-for-syntax unsupport-outside-problem-definition-msg "can not be used outside problem definition")


; instance structure
; a list wrapped in a struct
(struct dp-instance (fields))


(begin-for-syntax

  ; (and dp-parse-table (not dp-part-cert-env?)) => parsing instance part
  ; (and dp-parse-table dp-part-cert-env?) => parsing cert
  (define dp-parse-table (make-parameter #f))
  (define dp-part-cert-env? (make-parameter #f))
  (define dp-cur-field-id (make-parameter #f))

  #;(define (assert-parse-table-ref id-stx)
    (let ([entry (free-id-table-ref (dp-parse-table) id-stx #f)])
      (if entry
          entry
          (raise-syntax-error #f "undefined instance part" id-stx))))

  ; See decision-problem.rkt dp-parse-instance
  (define (parsed-entry-type a-entry)
    (car a-entry))
  (define (parsed-entry-idx a-entry)
    (cdr a-entry))
  
  ; get the field type descriptor from the parsing table
  ; use in an environment where ``dp-parse-table'' is parameterized
  (define (get-field-from-parsed field-name-stx [error-on-undefined #t])
    (let ([field-entry (free-id-table-ref (dp-parse-table) field-name-stx #f)])
      (if field-entry
          (parsed-entry-type field-entry)
          (if error-on-undefined
              (raise-syntax-error
               #f
               "undefined field"
               field-name-stx)
              #f))))

  ; an #f index means the field is a temporary value, not as a part of an instance value
  (define (get-field-index-from-parsed field-name-stx)
    (let ([field-type-stx (free-id-table-ref (dp-parse-table) field-name-stx #f)])
      (if
       field-type-stx
       (parsed-entry-idx field-type-stx)
       (raise-syntax-error
        #f
        "undefined field"
        field-name-stx))))

  ; get the index for list-ref the instance structure
  ; the 0-th position of instance is a symbol (see instance structure)
  (define (get-instance-field-index-from-parsed field-name-stx)
    (+ (get-field-index-from-parsed field-name-stx) 1))

  (define (instance-field-ref a-inst-stx field-name-stx)
    #`(list-ref (dp-instance-fields #,a-inst-stx)
                #,(get-instance-field-index-from-parsed field-name-stx)))

  ; currently not in use
  #;(define (add-field-to-parsed field-name-stx field-type-stx ind)
    (free-id-table-set (dp-parse-table) field-name-stx (cons field-type-stx ind)))

  (define (parsed-table-with-temp-field temp-field-name-stx temp-field-type-stx)
    (free-id-table-set (dp-parse-table) temp-field-name-stx (cons temp-field-type-stx #f)))

  ; maybe-size-stx : syntax object specifying size
  ; -> (or/c boolean? integer?)
  ; returns #f if no size is specified or specified as an instance field
  ; returns the integer size if size is specified as an integer constant
  (define (get-size-as-num maybe-size-stx)
    (cond
      [(not maybe-size-stx) #f]
      [(identifier? maybe-size-stx)
       (let ([field-type
              (dp-stx-type-info-field (get-field-from-parsed maybe-size-stx) type)])
         (if (equal? field-type 'natural)
             #f
             (raise-syntax-error
              #f
              "only a field of natural can be used as size"
              maybe-size-stx)))]
      [(exact-positive-integer?
        (syntax-e maybe-size-stx)) (syntax-e maybe-size-stx)]
      [else
       (raise-syntax-error
        #f
        "size must be a positive integer
         or a parameter previously defined"
        maybe-size-stx)]))

  (define (trace-upstream-to-field cur-layer the-inst)
    (if (identifier? cur-layer)
        (instance-field-ref the-inst cur-layer)
        (if (list? (dp-stx-info-field cur-layer upstream))
            #`(#,(dp-stx-info-field cur-layer upstream-combinator)
               #,@(let ([upstreams (dp-stx-info-field cur-layer upstream)])
                    (map (λ (i) #`(#,(list-ref (dp-stx-info-field cur-layer upstream-accessor) i)
                                   #,(trace-upstream-to-field
                                      (list-ref (dp-stx-info-field cur-layer upstream) i)
                                      the-inst)))
                         (range (length upstreams)))))
            #`(#,(dp-stx-info-field cur-layer upstream-accessor)
               #,(trace-upstream-to-field (dp-stx-info-field cur-layer upstream) the-inst)))))

  (define (dp-expand-part part-stx)
    (local-expand part-stx 'expression #f))
  (define (dp-expand-parts parts-stx)
    (map
     (λ (a-stx)
       (local-expand a-stx 'expression #f))
     (stx->list parts-stx)))

  ; old versions
  #;(define-syntax (dp-expand-part stx)
      (syntax-parse stx
        [(_ part-stx)
         #'(local-expand part-stx 'expression #f)]))
  #;(define-syntax (dp-expand-parts stx)
      (syntax-parse stx
        [(_ parts-stx)
         #'(map
            (λ (a-stx)
              (local-expand a-stx 'expression #f))
            (stx->list parts-stx))]))

)

; value-dependent contract combinator for value-independent values
; i.e. returns a contract accepting anything given any instance value
(define v-dep-any/c
  (λ (a-inst) any/c))


#;#'(begin (struct my-element ())
         (....  (struct/c my-element)))

; dynamic generic interfaces for objects
(define-values (prop:interface interfaced-struct? get-interface)
  (r:make-struct-type-property 'interface))

(define-values (prop:struct-constr has-struct-constr? struct-constr)
    (make-impersonator-property 'structural-constraint))

(define (r-symbolic-atom? x)
  (or (r:term? x)
      (r:union? x)))

; test if the structure contains symbolic values
; i.e., it can not goes to hash-ref (e.g. as key for mappings)
(define (dp-symbolic? x)
  (or (r-symbolic-atom? x)
      (and (interfaced-struct? x)
           (let ([sym? (assoc 'symbolic? (get-interface x))])
             (if sym?
                 ((cdr sym?) x)
                 #f)))))