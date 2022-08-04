#lang racket

(require rackunit
         "../private/problem-definition-core.rkt"
         "../private/decision-problem.rkt"
         "../lib/graph.rkt"
         "../lib/mapping.rkt"
         [rename-in "../private/primitive-data-type.rkt"
                    (dp-int-ge >=)
                    (dp-int-le <=)]
         [only-in rosette/safe
                  and nand or]
         racket/stxparam)
(require (prefix-in r: rosette/safe))

(decision-problem #:name set-cover
                  #:instance ([E is-a set]
                              [F is-a (set #:of-type (subset-of E))]
                              [K is-a natural])
                  #:certificate (subset-of F))

(define-set-cover-verifier a-inst a-cert
  (and
   (∀ [e ∈ (E a-inst)]
     (∃ [s ∈ a-cert]
        (set-∈ e s)))
   (>= (set-size a-cert) (K a-inst))))


;(create-set-cover-instance ([E (set 'a 'b 'c)] [F (set (set 'a))] [K 1]))
;(create-set-cover-instance ([E (set 'a 'b 'c)] [F (set 'a)] [K 1]))

;(create-set-cover-instance ([E (set (set 'a 'b) (set 'b 'c))] [F (set (set (set 'a 'b)))] [K 1]));
;(create-set-cover-instance ([E (set (set 'a 'b) (set 'b 'c))] [F (set (set (set 'a 'c 'd)))] [K 1]))

(decision-problem #:name test-g
                  #:instance ([G is-a graph]
                              [H is-a (subgraph-of G)]
                              [K is-a natural])
                  #:certificate (subset-of (vertices-of G) #:size K))

(define V1 (set 'x1 'x2 'x3 'x4 'x5))
(define E1 (set ('x1 . -e- . 'x2)
                ('x1 . -e- . 'x3)
                ('x2 . -e- . 'x3)
                ('x3 . -e- . 'x4)
                ('x4 . -e- . 'x5)
                ('x5 . -e- . 'x1)))

(define V2 (set 'x1 'x2 'x3 'x4))
(define E2 (set ('x1 . -e- . 'x2) ('x2 . -e- .'x3) #;('x1 . -e- . 'x4)))
(define sg1 (create-test-g-instance ([G (create-graph V1 E1)]
                                     [H (create-graph V2 E2)]
                                     [K 1])))

(define-test-g-verifier a-inst a-cert
  (and
   (∀ [u ∈ (vertices-of (G a-inst))]
     (∀ [v ∈ (neighbors (G a-inst) u)]
        (nand
         (set-∈ u a-cert)
         (set-∈ v a-cert))))
   #;(>= (set-size a-cert) (K a-inst))))


(decision-problem #:name test-m
                  #:instance ([A is-a set]
                              [B is-a set]
                              [M is-a (mapping #:from A #:to (the-set-of (subset-of B)) #:disjoint)])
                  #:certificate (subset-of B))


(define tm1 (create-test-m-instance ([A (set 'a 'b 'c)]
                                     [B (set 1 2 3 4 5)]
                                     [M (mapping ['a ~> (set 1 2)] ['b ~> (set 3 4)]
                                                 ['c ~> (set 5)]
                                                 #;['c ~> (set 5 6)])])))

;(lookup (M tm1) 'd)
#;((M tm1) 'd)

