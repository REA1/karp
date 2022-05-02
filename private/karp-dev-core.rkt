#lang racket
(require "problem-definition-core.rkt")

(provide (except-out
          (all-from-out "problem-definition-core.rkt")
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
                     [dp-equal? equal?]))