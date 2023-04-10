#lang racket

(require "../reduction-base.rkt")

(provide (except-out
          (all-from-out "../reduction-base.rkt")
          dp-int-plus
          dp-int-minus
          dp-int-gt
          dp-int-ge
          dp-int-lt
          dp-int-le
          dp-int-eq
          dp-int-max
          dp-int-min
          dp-equal?
          dp-even?
          dp-odd?
          dp-expt
          dp-mod)
         max
         min
         (rename-out [dp-int-plus +]
                     [dp-int-minus -]
                     [dp-int-mult *]
                     [dp-int-gt >]
                     [dp-int-ge >=]
                     [dp-int-lt <]
                     [dp-int-le <=]
                     [dp-int-eq =]
                     [dp-equal? equal?]
                     [dp-even? even?]
                     [dp-odd? odd?]
                     [dp-expt expt]
                     [dp-mod modulo]))