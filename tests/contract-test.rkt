#lang racket

(require "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt")

#;(test 1 'b1)

(define-simple-contract/kc gt0/kc (v1)
  (> v1 0)
  "positive")

(define-simple-contract/kc gt5/kc (v1)
  (> v1 5)
  "greater than 5")

(define/contract/kc (test1 x)
  (->k ((x (and/kc gt0/kc gt5/kc))) any/kc)
  x)

(test1 6)
(test1 5)

(define/contract/kc (test-rest . rest)
  (->k #:rest [rst gt0/kc] any/kc)
  rest)

;(test-rest 1 2 3 4 5)
;(test-rest 0 -1 0 3 4)
;(test-rest 2 -1 0 3 4)
;(test-rest 2 1 2 0 4)