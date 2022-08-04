#lang racket/gui

(require
  (rename-in "../private/core-structures.rkt"
             [set k-set])
  mrlib/expandable-snip)

(define set-snip-class%
  (class snip-class%
    (super-new)))
   
(define set-snip-class (new set-snip-class%))


#;(define (render-set/snip a-set)
  )