#lang racket

(require "../private/core-structures.rkt"
         "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt"
         "../lib/graph.rkt"
         racket/stxparam)


(define V1 (a-set 'x1 'x2 'x3 'x4 'x5))
(define E1 (a-set ('x1 . -e- . 'x2)
                  ('x1 . -e- . 'x3)
                  ('x2 . -e- . 'x3)
                  ('x3 . -e- . 'x4)
                  ('x4 . -e- . 'x5)
                  ('x5 . -e- . 'x1)))

(define/contract/kc (test x)
  (->k ([x dp-graph-u/kc]) any/kc)
  x)

(define V2 (set 'x1 'x2 'x3 'x4 'x5))
(define E2 (set ('x1 . -e- . 'x2)
                ('x2 . -e- . 'x3)))
#;(test E1)
(test (create-graph V1 E1))