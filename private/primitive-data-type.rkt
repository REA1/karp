#lang racket

(require "verifier-type.rkt"
         "karp-contract.rkt"
         "problem-definition-utility.rkt"
         racket/random
         [for-syntax racket/struct
                     racket/syntax
                     syntax/parse
                     racket/match]
         [for-meta 2 racket/base
                     syntax/parse]
         (prefix-in r: rosette/safe))

(provide
 fresh-symbolic-bool
 fresh-symbolic-int
)


;; symbolic
(define (fresh-symbolic-bool)
  (r:define-symbolic* x r:boolean?)
  x)

(define (fresh-symbolic-int)
  (r:define-symbolic* x r:integer?)
  x)

;; symbol

(provide symbol
         symbol/kc
         gen-random-sym-el)

; type object representing Symbol
; the opaque element type, including symbols and dont-care elements
; only equality is defined
(begin-for-syntax
  (provide tSymbol)
  
  (struct ty-Symbol () #:transparent
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Symbol)
        (λ (self) '())))])
  
  (define-match-expander tSymbol
    (syntax-parser
      [(_) #'(ty-Symbol)])
    (syntax-parser
      [(_) #'(ty-Symbol)]))
)

(define-simple-contract/kc symbol/kc (v)
  (symbol? v)
  "expects a symbol")

(define-syntax (symbol stx)
  (if (dp-parse-table)
      ; only valid for inst
      (if (not (dp-part-cert-env?))
          (dp-stx-type-desc
           (generate-temporary #'symbol)
           type 'symbol
           kv-type-object #'(tSymbol)
           atomic? #t
           ctc #'symbol/kc
           v-dep-ctc #'v-dep-any/kc
           type-data '()
           accessors '()
           generator #`(λ (a-inst)
                         (λ () (gen-random-sym-el '#,(dp-cur-field-id)))))
          (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (raise-syntax-error 'symbol "unsupported" stx)))

; generate a set of symbols
; el-name: symbol?
(define (random-symbol-el set-name max-n)
  (let* ([k (random 1 (+ max-n 1))]
         [el-name (string-downcase (symbol->string set-name))]
         [the-el (string->symbol (string-append el-name (number->string k)))])
    the-el))

; XXX: magic numbers scattered everywhere
(define (gen-random-sym-el set-name)
  (random-symbol-el set-name 20))


;; Boolean

(provide boolean)

; type object representing Bool
(begin-for-syntax
  (provide tBool)

  (struct ty-Bool () #:transparent
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Bool)
        (λ (self) '())))])
  
  (define-match-expander tBool
    (syntax-parser
      [(_) #'(ty-Bool)])
    (syntax-parser
      [(_) #'(ty-Bool)]))
  
)

(define-simple-contract/kc boolean/kc (v)
  (boolean? v)
  "expects a boolean")

(define-syntax (boolean stx)
  (syntax-parse stx
    [(_)
     (if (dp-parse-table)
         ; same for inst and cert env
         (dp-stx-type-desc
          (generate-temporary #'boolean)
          type 'boolean
          kv-type-object #'(tBool)
          atomic? #t
          ctc #'boolean/kc
          v-dep-ctc #'v-dep-any/kc
          type-data '()
          accessors '()
          symbolic-constructor #'(λ (a-inst) dp-symbolic-boolean)
          solution-decoder #'dp-boolean-from-sol
          null-object #'dp-null-boolean
          generator #'(λ (a-inst)
                        (λ () (gen-random-bool))))
         (raise-syntax-error 'boolean unsupport-outside-problem-definition-msg stx))]
    [_:id #'(boolean)]))

(define (gen-random-bool)
  (random-ref (list #t #f)))

(define dp-null-boolean -1)

(define (dp-symbolic-boolean)
  (values
   (fresh-symbolic-bool)
   '()))

(define (dp-boolean-from-sol sym-n a-sol)
  (if (r:unsat? a-sol) dp-null-boolean
      ; use -1 as default
      (hash-ref (r:model a-sol) sym-n #f) ; alternatively use (evaluate sym-n a-sol) (?)
   ))


;
; natural number
;
;

; wrapped natural
;
; val : (or/c natural? boolean?) --- the value of the natural, with #f indicating no solution
; size : (or/c 'const 'poly 'exp)  --- the size of the value to the input length
; Note: An integer has size exponential to the input length if either:
;       1. it represents a numerical value from the input
;       2. it is the result of the integer exponentiation operator with exponent with size 'poly
;       3. it is the result of an arithmetic operator with at least one of the operating having size 'exp
;       An integer has size polynomial to the input length if either:
;       1. it represents a count or cardinality value from the input
;       2. it is the result of size/length operators for data structures, i.e. set-size
;       3. it is the result of an arithmetic operator with at least one of with size 'poly but no 'exp
;       All integer literals in the program code (they are not part of input) are considered constants
; XXX:  The 'const is not fully functioning currently because we can not tell if the result of counting
;       from a structure is constant unless we know the structure itself is constant
;       e.g. whether (set-size a-set) has size 'poly or 'const depends on whether a-set is constant

(provide
 dp-wrap-if-raw-int
 dp-int-wrap
 dp-int-unwrap
 dp-int-size-of
 dp-int-not-exp-size/kc
 dp-int-not-exp-size/c
 dp-int-max-size
 dp-int-lst-max-size

 dp-integer-w/kc
 dp-natural-w/kc
 
 ; everything from below should be renamed and exposed to the user
 dp-int-plus
 dp-int-minus
 dp-int-mult
 dp-int-gt
 dp-int-ge
 dp-int-lt
 dp-int-le
 dp-int-eq
 dp-int-max
 dp-int-min
 ; only exposed in reduction
 dp-expt
 dp-mod
 dp-even?
 dp-odd?)

(provide natural
         gen-random-natural)

(define (dp-int-eq x y [recursive-equal? #f])
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (r:= raw-x raw-y)))

; type object representing Int
; int type, one type for natural and integer
(begin-for-syntax
  (provide tInt)
  
  (define-match-expander tInt
    (syntax-parser
      [(id) #'(ty-Int)])
    (syntax-parser
      [(id) #'(ty-Int)]))

  (struct ty-Int () #:transparent
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Int)
        (λ (self) '())))])
)

(provide (struct-out dp-integer))

(struct dp-integer (val size) #:transparent
  #:methods gen:equal+hash
          [(define equal-proc dp-int-eq)
           (define (hash-proc a-dp-int recursive-equal-hash)
             (equal-hash-code (dp-integer-val a-dp-int)))
           (define (hash2-proc a-dp-int recursive-equal-hash)
             (equal-secondary-hash-code (dp-integer-val a-dp-int)))]
  #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-dp-int port mode)
                 (if (dp-integer-val the-dp-int)
                     (if (equal? (dp-int-size-of the-dp-int) 'exp)
                         (fprintf port "~aₑ" (dp-integer-val the-dp-int))
                         (fprintf port "~aₚ" (dp-integer-val the-dp-int)))
                     (fprintf port "null (no solution)"))))])

(define dp-null-integer (dp-integer #f #f))

; check and wrap int if necessary
(define (dp-integer-w/kc [size 'const])
  (kc-contract (v the-srcloc name context [predicate? #f])
    (if (dp-integer? v)
        (if (and (integer? (dp-integer-val v)) (symbol? (dp-integer-size v)))
            ; overriding the size if size specified
            (if size (dp-int-wrap (dp-int-unwrap v) size) v)
            (error "integer internal error"))
        (if (integer? v)
            (dp-int-wrap v (if size size 'const))
            (contract-fail/kc the-srcloc name "expects an integer" context v predicate?)))))

(define (dp-integer/c x)
  (or/c (struct/c dp-integer integer? symbol?)
        (λ (x) (and (not (dp-integer-val x)) (not (dp-integer-size x))))))

(define (dp-natural-w/kc [size 'const])
  (kc-contract (v the-srcloc name context [predicate? #f])
    (if (dp-integer? v)
        (if (and (integer? (dp-integer-val v)) (symbol? (dp-integer-size v)))
            (if (natural? (dp-integer-val v))
                ; overriding the size if size specified
                (if size (dp-int-wrap (dp-int-unwrap v) size) v)
                (contract-fail/kc
                 the-srcloc name "expects a natural number (nonegative integer)"
                 context v predicate?))
            (error "integer internal error"))
        (if (natural? v)
            (dp-int-wrap v (if size size 'const))
            (contract-fail/kc the-srcloc name "expects a natural number" context v predicate?)))))

(define (dp-natural/c x)
  (or/c (struct/c dp-integer natural? symbol?)
        (λ (x) (and (not (dp-integer-val x)) (not (dp-integer-size x))))))

(define (dp-symbolic-natural)
  (values
   (fresh-symbolic-int)
   (r:list
    (r:λ (n) (r:>= n 0)))))

(define (dp-natural-from-sol sym-n a-sol)
  (if (r:unsat? a-sol) dp-null-integer
      ; use 0 as default
      (hash-ref (r:model a-sol) sym-n 0) ; alternatively use (evaluate sym-n a-sol) (?)
   ))
;
; -----------------------------------------

;
; wrapped arithmetic operations
;
(define (dp-wrap-if-raw-int x [size 'const])
  (if (r:integer? x)
      (dp-int-wrap x size)
      x))

(define wrap-count 0)

(define (dp-int-wrap x [size 'const])
  ;(set! wrap-count (+ wrap-count 1))
  ;(pretty-print "w:")
  ;(pretty-print wrap-count)
  (cond [(r:integer? x) (dp-integer x size)]
        [(dp-integer? x) x]
        [else (error "expects an integer, gets" x)]))

(define unwrap-count 0)

(define (dp-int-unwrap x)
  ;(set! unwrap-count (+ unwrap-count 1))
  ;(pretty-print "u:")
  ;(pretty-print unwrap-count)
  (cond [(r:integer? x) x]
        [(dp-integer? x) (dp-integer-val x)]
        [else (error "expects an integer, gets" x)]))

(define (dp-int-size-of x)
  (cond [(r:integer? x) 'const]
        [(dp-integer? x) (dp-integer-size x)]
        [else (error "expects an integer, gets" x)]))

; exp > poly > const
(define (dp-int-max-size x y)
 (let ([size-x (dp-int-size-of x)]
       [size-y (dp-int-size-of y)])
  (cond [(or (equal? size-x 'exp)
             (equal? size-y 'exp)) 'exp]
        [(or (equal? size-x 'poly)
             (equal? size-y 'poly)) 'poly]
        [else 'const])))

(define (dp-int-not-exp-size/c x)
  (if (equal? (dp-int-size-of x) 'exp)
      #f
      #t))

(define-simple-contract/kc dp-int-not-exp-size/kc (v)
  (equal? (dp-int-size-of v) 'exp)
  "expects a value being polynomial of the input length")

(define (dp-int-lst-max-size lst)
  (let ([size-lst (map dp-int-size-of lst)])
    (r:cond [(r:member 'exp size-lst) 'exp]
          [(r:member 'poly size-lst) 'poly]
          [r:else 'const])))

(define/contract/kc (dp-int-plus . xs)
  (->k #:rest [xs (dp-integer-w/kc #f)] any/kc)
  (let ([raw-xs (map (λ (x) (dp-int-unwrap x)) xs)])
    (dp-integer (r:apply r:+ raw-xs) (dp-int-lst-max-size xs))))

(define/contract/kc (dp-int-minus x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) any/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
  (dp-integer (r:- raw-x raw-y) (dp-int-max-size x y))))

(define/contract/kc (dp-int-mult . xs)
  (->k #:rest [xs (dp-integer-w/kc #f)] any/kc)
  (let ([raw-xs (map (λ (x) (dp-int-unwrap x)) xs)])
  (dp-integer (r:apply r:* raw-xs) (dp-int-lst-max-size xs))))

(define/contract/kc (dp-int-gt x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) boolean/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (r:> raw-x raw-y)))

(define/contract/kc (dp-int-ge x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) boolean/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (r:>= raw-x raw-y)))

(define/contract/kc (dp-int-lt x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) boolean/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (r:< raw-x raw-y)))

(define/contract/kc (dp-int-le x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) boolean/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (r:<= raw-x raw-y)))

(define/contract/kc (dp-int-max x0 . xs)
  (->k #:rest [xs (dp-integer-w/kc #f)] any/kc)
  (let ([raw-x0xs (map (λ (x) (dp-int-unwrap x)) (cons x0 xs))])
  ; XXX: Is it possible a int has larger size but smaller value?
  ; size of the result is set as the maximum size among all integer, regarless of value
  (dp-integer (r:apply r:max raw-x0xs) (dp-int-lst-max-size (cons x0 xs)))))

(define/contract/kc (dp-int-min x0 . xs)
  (->k #:rest [xs (dp-integer-w/kc #f)] any/kc)
  (let ([raw-x0xs (map (λ (x) (dp-int-unwrap x)) (cons x0 xs))])
  ; XXX: Is it possible a int has larger size but smaller value?
  ; size of the result is set as the maximum size among all integer, regarless of value
  (dp-integer (r:apply r:min raw-x0xs) (dp-int-lst-max-size (cons x0 xs)))))

; operators in reduction
(define/contract/kc (dp-expt x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) any/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    (dp-integer (expt raw-x raw-y)
                (cond [(or
                        (equal? (dp-int-size-of x) 'exp)
                        (not (equal? (dp-int-size-of y) 'const))) 'exp]
                      [(equal? (dp-int-size-of x) 'const) 'const]
                      [else 'poly]) ; (equal? (dp-size-of-integer x) 'poly)
                ; equivalent to:
                #;(if (equal? (dp-size-of-integer x) 'exp)
                    'exp
                    (if (equal? (dp-size-of-integer y) 'const)
                        (if (equal? (dp-size-of-integer x) 'const)
                            'const
                            'poly)
                        'exp))
                )))

(define/contract/kc (dp-mod x y)
  (->k ([x (dp-integer-w/kc #f)] [y (dp-integer-w/kc #f)]) any/kc)
  (let ([raw-x (dp-int-unwrap x)]
        [raw-y (dp-int-unwrap y)])
    ; XXX: size can be made more precise?
    (dp-integer (modulo raw-x raw-y) (dp-int-max-size x y))))

(define/contract/kc (dp-even? x)
  (->k ([x (dp-integer-w/kc #f)]) any/kc)
  (let ([raw-x (dp-int-unwrap x)])
    (even? raw-x)))

(define/contract/kc (dp-odd? x)
  (->k ([x (dp-integer-w/kc #f)]) any/kc)
  (let ([raw-x (dp-int-unwrap x)])
    (odd? raw-x)))

; The Natural


(define (gen-random-natural a b [size #f])
  (let ([a (dp-int-unwrap a)]
        [b (dp-int-unwrap b)])
    (if size
        (dp-integer (random a b) size)
        (random a b))))

(define-syntax (natural stx)
  (syntax-parse stx
    [(_ (~optional (~or #:cardinal (~and #:numeric pv-numeric))))
     #`(integer #:natural (~? pv-numeric #:cardinal))]
    [_:id #'(natural)]))

; old version
#;(define-syntax (natural stx)
  (syntax-parse stx
    [(_)
     (if (dp-parse-table)
         ; same for inst and cert env
         (dp-stx-type-desc
          (generate-temporary #'natural)
          type 'natural
          kv-type-object #'(tInt)
          atomic? #t
          ctc #'natural/c
          v-dep-ctc #'v-dep-any/c
          type-data '()
          accessors '()
          ; Note: natural can not be used as solvable
          ;symbolic-constructor #'(λ (a-inst) dp-symbolic-natural)
          ;solution-decoder #'dp-natural-from-sol
          ;null-object #'dp-null-natural
          generator #'(λ (a-inst)
                        (λ ()
                          (gen-random-natural)))
          )
         (raise-syntax-error 'natural unsupport-outside-problem-definition-msg stx))]
    [_:id #'(natural)]))


; TODO: add generate random integer
(define-syntax (integer stx)
  (syntax-parse stx
    [(_ (~optional (~and #:natural pv-natural))
        (~optional (~or #:cardinal (~and #:numeric pv-numeric))))
     (if (dp-parse-table)
         ; same for inst and cert env
         (dp-stx-type-desc
          (generate-temporary #'integer)
          type (if (attribute pv-natural) 'natural 'integer)
          kv-type-object #'(tInt)
          atomic? #t
          ctc (let ([size (if (attribute pv-numeric) #''exp #''poly)])
                (if (attribute pv-natural)
                  #`(dp-natural-w/kc #,size)
                  #`(dp-integer-w/kc #,size)))
          ;wrapper #`(λ (x) (dp-integer x #,(if ())))
          v-dep-ctc #'v-dep-any/kc
          type-data '()
          accessors '()
          ; Note: integers can not be used as solvable
          ;symbolic-constructor #'(λ (a-inst) dp-symbolic-natural)
          ;solution-decoder #'dp-natural-from-sol
          ;null-object #'dp-null-natural
          generator #`(λ (a-inst)
                        (λ ()
                          (gen-random-natural
                           ; XXX: magic number
                           1
                           12
                           #,(if (attribute pv-numeric)
                                 #''exp
                                 #''poly))))
          )
         (raise-syntax-error 'integer unsupport-outside-problem-definition-msg stx))]
    [_:id #'(integer)]))

;-------------------------------------------------
; type annotation for primitive operators
;
;
; Note: the YYY in YYY-typed-rewriter will be used
;       by the typechecker to match against the id
;       of the operator to determine the operator
;       type. Hence ``r:and'' will only match
;       ``r:and'' but not ``and''
; See ``dp-typecheck-rewrite'' in decision-problem
;
;-------------------------------------------------

(kv-func-type-annotate + ((tInt) (tInt) (tInt)) "two numbers")
(kv-func-type-annotate - ((tInt) (tInt) (tInt)) "two numbers")
(kv-func-type-annotate * ((tInt) (tInt) (tInt)) "two numbers")
(kv-func-type-annotate > ((tInt) (tInt) (tBool)) "two numbers")
(kv-func-type-annotate >= ((tInt) (tInt) (tBool)) "two numbers")
(kv-func-type-annotate < ((tInt) (tInt) (tBool)) "two numbers")
(kv-func-type-annotate <= ((tInt) (tInt) (tBool)) "two numbers")
(kv-func-type-annotate = ((tInt) (tInt) (tBool)) "two numbers")
;(kv-func-type-annotate r:and ((tBool) (tBool) (tBool)) "two booleans")
(provide and-typed-rewriter)
(define-syntax and-typed-rewriter
  (λ (arg-lst)
    (match arg-lst
      [(list (cons _ (tBool)) ...)
       (λ (stx) (cons stx (tBool)))]
      [_ (syntax-parser
           [(and arg ...)
            (raise-syntax-error #f
                                (format "expects booleans, gets ~a"
                                        (map get-τb arg-lst))
                                #'(and arg ...)
                                #'and)])])))
#;(kv-func-type-annotate r:nand ((tBool) (tBool) (tBool)) "two booleans")
(provide nand-typed-rewriter)
(define-syntax nand-typed-rewriter
  (λ (arg-lst)
    (match arg-lst
      [(list (cons _ (tBool)) ...)
       (λ (stx) (cons stx (tBool)))]
      [_ (syntax-parser
           [(nand arg ...)
            (raise-syntax-error #f
                                (format "expects booleans, gets ~a"
                                        (map get-τb arg-lst))
                                #'(nand arg ...)
                                #'nand)])])))
#;(kv-func-type-annotate r:or ((tBool) (tBool) (tBool)) "two booleans")
(provide or-typed-rewriter)
(define-syntax or-typed-rewriter
  (λ (arg-lst)
    (match arg-lst
      [(list (cons _ (tBool)) ...)
       (λ (stx) (cons stx (tBool)))]
      [_ (syntax-parser
           [(or arg ...)
            (raise-syntax-error #f
                                (format "expects booleans, gets ~a"
                                        (map get-τb arg-lst))
                                #'(or arg ...)
                                #'or)])])))
(kv-func-type-annotate not ((tBool) (tBool)) "one booleans")
;------------------------------------------
; end of primitive operators
;------------------------------------------