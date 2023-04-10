#lang racket

(require "private/problem-definition-core.rkt"
         "private/decision-problem.rkt"
         (except-in rosette/safe min max count define))

(provide #%module-begin #%app #%datum #%top #%top-interaction
         (except-out
          (all-from-out "private/problem-definition-core.rkt")
          dp-int-plus
          dp-int-minus
          dp-int-gt
          dp-int-ge
          dp-int-lt
          dp-int-le
          dp-int-eq
          dp-equal?
          dp-int-max
          dp-int-min
          dp-expt
          dp-mod)
         (rename-out [dp-int-plus +]
                     [dp-int-minus -]
                     [dp-int-mult *]
                     [dp-int-gt >]
                     [dp-int-ge >=]
                     [dp-int-lt <]
                     [dp-int-le <=]
                     [dp-int-eq =]                    
                     [dp-equal? equal?])
         (all-from-out "private/decision-problem.rkt")

         require
         provide
         and
         or
         not
         xor
         nand
         implies
         quote)