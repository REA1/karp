#lang racket

;; custom constract system for Karp
;; for displaying better error message and avoid compatibility issue with Rosette

(require "problem-definition-utility.rkt"
         "modified/error.rkt"
         (for-syntax racket/syntax
                     syntax/parse
                     syntax/stx
                     racket/list
                     racket/syntax-srcloc)
         [for-meta 2 syntax/parse
                     racket/base]
         racket/string
         racket/stxparam
         racket/syntax-srcloc)

(provide define/contract/kc
         define-simple-contract/kc
         make-simple-contract/kc
         kc-contract
         contracted-v/kc
         make-predicate/kc
         contract-fail/kc
         and/kc
         or/kc
         any/kc
         v-dep-any/kc

         dp-kc-unprotected-env?
         without-protection/kc
         make-predicate/kc

         (for-syntax ordinal-numeral))

; used to disable contract protecting for language constructs defined by define/contract/kc
(define-syntax-parameter dp-kc-unprotected-env? #f)

(define-syntax (without-protection/kc stx)
  (syntax-parse stx
    [(_ body ...)
     #'(syntax-parameterize ([dp-kc-unprotected-env? #t])
         body ...)]))

;; Convention: all some-contract/kc will take the following arguments
;; v : any/c           -- the value being checked
;; the-srcloc : srcloc? -- the source location indicating where the error is
;;                        in user's code to use in the error message
;; name : symbol?      -- name part of the error message
;; context : cons?     -- the context to add to the error message
;; [predicate?] : boolean?  -- return #t / #f instead of projection (pass value or triggering error)
;;                         (false by default)

; no longer in use
; causing ambiguity
(begin-for-syntax
  (define-syntax-class dom/kc
    #:attributes (arg-id-kc dep-part arg/kc)
    (pattern
      (~or [arg-id:id
            (~optional (~and (dep-id:id ...) dep))
            ctc]
           ctc)
      #:attr arg-id-kc (if (attribute arg-id) #'arg-id (generate-temporary 'arg-id))
      #:attr dep-part (if (attribute dep) #'dep #''()) 
      #:attr arg/kc #'ctc))
)

(begin-for-syntax
  (define-syntax (ordinal-numeral stx)
    (syntax-parse stx
      [(_ i)
       #`(cond [(equal? i 1) 'st]
               [(equal? i 2) 'nd]
               [(equal? i 3) 'rd]
               [else 'th])])))

; Note: it is assumed that only language constructs in user's code are protected.
;       protecting internal code would lead to srcloc pointing to internal files
;       Since the user's code is first-ordered, higher order usage of the function
;       defined by this construct will not be protected.
; Note2: the dep-part exists only for the purpose of
;       keeping format consistent with the Racket contract 
;       library. It has no actual use.
; Note3: -list is instead of -lst here in names
(define-syntax (define/contract/kc stx)
  (syntax-parse stx
    [(_ (name arg-id:id ...)
        ((~datum ->k)
         ([arg-id-kc:id
           (~optional (~and (dep-id:id ...) dep-part) #:defaults ([dep-part #''()]))
           arg/kc] ...)
         ret/kc)
      body ...)
     #:with arg-id-kc-list #'(arg-id-kc ...)
     #:with arg-dep-list #'(dep-part ...)
     #:with arg/kc-list #'(arg/kc ...)
     #:with un#-in-template (quote-syntax unsyntax)
     #:with un#@-in-template (quote-syntax unsyntax-splicing)
     #`(begin        
         (define (unprotected arg-id ...)
           (syntax-parameterize ([dp-kc-unprotected-env? #t])
             body ...))
         (define-syntax (name stx-inner)
           (syntax-parse stx-inner
             [_:id #'unprotected]
             [(_ args-inner (... ...))
              #:with arg-inner-list #'(args-inner (... ...))
              #:with arg-passed (generate-temporaries #'arg-id-kc-list)
              #:fail-when (not (equal? (length (stx->list #'arg-inner-list))
                                       (length (stx->list #'arg-id-kc-list))))
                          (format "wrong number of arguments, expected: ~v"
                                  (length (stx->list #'arg-id-kc-list)))
              (if (or (syntax-parameter-value #'dp-solver-env?)
                      (syntax-parameter-value #'dp-kc-unprotected-env?))
                  #'(unprotected args-inner (... ...))                  
                  #`(let (#,@(for/list ([arg (stx->list #'arg-inner-list)]
                                        [arg-kc (stx->list #'arg-id-kc-list)])
                               #`[#,arg-kc #,arg]))
                      (ret/kc
                       (let (#,@(for/list ([i (range 1 (add1 (length (stx->list #'arg-id-kc-list))))]
                                           [arg (stx->list #'arg-inner-list)]
                                           [arg-kc (stx->list #'arg-id-kc-list)]
                                           [kc (stx->list #'arg/kc-list)]
                                           [arg2 (stx->list #'arg-passed)])
                                  #`[#,arg2
                                     #,(quasisyntax/loc arg
                                           ((un#-in-template kc)
                                            (un#-in-template arg-kc)
                                            (syntax-srcloc #'(un#-in-template arg))
                                            'name
                                            (list (format "the ~v~s argument of ~s"
                                                          (un#-in-template i)
                                                          '(un#-in-template
                                                            (ordinal-numeral i))
                                                          'name))))]))
                         (unprotected #,@#'arg-passed))                       
                       #,(syntax-srcloc stx-inner)
                       'name
                       (list #,(format "the return value of ~s" 'name))
                       
                       ; use the srcloc of the use location, which is stx-inner to guide the error
                       #;#,(quasisyntax/loc stx-inner 
                          (unprotected
                           (un#@-in-template
                            (for/list ([arg (stx->list #'arg-inner-list)]
                                       [arg-kc (stx->list #'arg-id-kc-list)]
                                       [kc (stx->list #'arg/kc-list)])
                                ; use #'#,stx-inner to use the srcloc of the whole expression
                                #`(#,kc #,arg-kc (syntax-srcloc #'#,arg #;#'#,stx-inner))))
                           )) ))  )])))]
    [(_ (name . rest)
      ((~datum ->k) #:rest [rst arg/kc] ret/kc) body ...)     
     #:with un#-in-template (quote-syntax unsyntax)
     #:with un#@-in-template (quote-syntax unsyntax-splicing)
     #`(begin
         (define (unprotected . rest)
           (syntax-parameterize ([dp-kc-unprotected-env? #t])
             body ...))
         (define-syntax (name stx-inner)
           (syntax-parse stx-inner
             [_:id #'unprotected]
             [(_ args-inner (... ...))
              #:with arg-inner-list #'(args-inner (... ...))
              (if (or (syntax-parameter-value #'dp-solver-env?)
                      (syntax-parameter-value #'dp-kc-unprotected-env?))
                  #'(unprotected args-inner (... ...))
                  (let
                   ([args-protected
                     (let ([arg-list (syntax->list #'arg-inner-list)])
                       (for/list ([i (range 1 (+ (length arg-list) 1))]
                                  [arg arg-list])
                         (quasisyntax/loc arg
                           ((un#-in-template #'arg/kc)
                            (un#-in-template arg)
                            (syntax-srcloc #'(un#-in-template arg))
                            'name
                            (list (format "the ~v~s argument of ~s"
                                          (un#-in-template i)
                                          '(un#-in-template
                                            (cond [(equal? i 1) 'st]
                                                  [(equal? i 2) 'nd]
                                                  [(equal? i 3) 'rd]
                                                  [else 'th]))
                                          'name))))))])
                    #`(ret/kc
                       (unprotected #,@args-protected)                        
                       #,(syntax-srcloc stx-inner)
                       'name
                       (list #,(format "the return value of ~s" 'name)))))])))]))

;
; a kc-contract, i.e. some-contract/kc is just a lambda (see the convention above)
; Note: contracts protecting for internal language constructs are disabled in the contracts itself,
;       i.e., there is no protection in the condition part
(define-syntax (kc-contract stx)
  (syntax-parse stx
    [(_ (v the-srcloc name context [predicate? #f]) body ...)
     #'(syntax-parameterize ([dp-kc-unprotected-env? #t])
         (λ (v the-srcloc name context [predicate? #f]) body ...))]))

; make a contract checking a single predicate (i.e., condition)
(define-syntax (make-simple-contract/kc stx)
  (syntax-parse stx
    [(_ (v-id:id) condition msg-fail)
     #'(kc-contract (v the-srcloc name context [predicate? #f])
            (if ((λ (v-id) condition) v)
                (if predicate? #t v) ; avoid confusion when v itself is #f
                (contract-fail/kc the-srcloc name msg-fail context v predicate?)))]))

(define-syntax (define-simple-contract/kc stx)
  (syntax-parse stx
    [(_ name/kc (v-id:id) condition msg-fail)
     #'(define name/kc (make-simple-contract/kc (v-id) condition msg-fail))
     #;#'(define (name/kc v the-srcloc name context [predicate? #f])
         (if ((λ (v-id)
                condition) v)
             v
             (contract-fail/kc the-srcloc name msg-fail context v predicate?)))]))

; pass the value through contract, check turned off in solver/unprotected environment
; as ```contract''' of Racket
(define-syntax (contracted-v/kc stx)
  (syntax-parse stx
    [(_ ctc v the-srcloc name context)
      (if (or (syntax-parameter-value #'dp-solver-env?)
              (syntax-parameter-value #'dp-kc-unprotected-env?))
          #'v
          #'(ctc v the-srcloc name context))]))

; shortcut to get the predicate corresponding to a kc/contract
(define ((make-predicate/kc ctc) v)
  (ctc v #f #f #f #t))

(define (contract-fail/kc srcloc name msg context v [predicate? #f])
  (if predicate?
      #f
      (error* srcloc name msg
              #:continued (string-append "in " (string-join context " of \n "))
              "given" v)))

(define (any/kc v the-srcloc name context [predicate? #f])
  (if predicate? #t v))

(define (none/kc v the-srcloc name context [predicate? #f])
  (contract-fail/kc the-srcloc name "no value shall pass" context v predicate?))

(define v-dep-any/kc
  (const any/kc))

; XXX(?): might not not handle the case when v itself is #f
; Note: guaranteed to shortcut
(define (and/kc . kcs)
  (λ (v the-srcloc name context [predicate? #f])
    (call/cc
     (λ (return)
       (let rec ([acc v]
                 [rest kcs])
         (if (null? rest)
             ; return to #t when predicate? is #t (for the case when v itself is #f)
             (if predicate? #t acc)
             ; when predicate? is #f, the error is triggered here 
             ; causing automatic shortcut
             (let ([result ((car rest) v the-srcloc name context predicate?)])
               (rec (if predicate?
                        ; when predicate? is #t, enforce shortcut
                        (if (not result)
                            (return result)
                            acc) ; equivalent to ``(and acc result)''
                        result)
                 (cdr rest)))))))))

(define (or/kc msg . kcs)
  (λ (v the-srcloc name context [predicate? #f])
    (if (ormap (λ (ctc) (ctc v the-srcloc name context #t)) kcs)
        (if predicate? #t v)
        (contract-fail/kc the-srcloc name msg context v predicate?))))


