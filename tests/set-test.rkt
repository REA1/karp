#lang racket

(require "../private/core-structures.rkt"
         "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt"
         [rename-in "../private/primitive-data-type.rkt"
                    (dp-int-ge >=)]
         racket/stxparam)

(define a (set 1 2 3))
(as-set a)
(define b (set (set 1 2 3)))
(define c (set (set 1 2) (set 1 2 3)))
(define d (set (set 1 2 3) (set 1 2 4)))

#;(as-set 1)

(define/contract/kc (set-set a-set)
  (->k ([x (and/kc
            (dp-setof/kc dp-set/kc)
            ((dp-setof-d/kc dp-subset-of-d/kc) a))]) any/kc)
  a-set)

;(set-set 1)

;(set-∪ b a)
;(set-∩ b 1)

#;(syntax-parameterize ([dp-solver-env? #t])
  #;(set-size 1)
  (set-∪ b 1))
#;(define/contract/kc (no-arg-test)
  (->k () dp-set/kc)
  (set 1))

#;(no-arg-test)

#;(syntax-parameterize ([dp-solver-env? #t])
  (∀ [x ∈ d] (>= (set-size x) 1)))