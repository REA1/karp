#lang racket

(require "reduction-base.rkt"
         (except-in rosette/safe argmin argmax min max count define))

(provide #%module-begin #%app #%datum #%top #%top-interaction
         (except-out
          (all-from-out "reduction-base.rkt")
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
         require
         provide
         even?
         odd?
         and
         or
         not
         xor
         nand
         implies
         quote
         if
         pretty-print
         )
