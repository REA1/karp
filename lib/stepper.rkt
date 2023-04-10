#lang racket/gui

(require (rename-in
          (except-in "../reduction-base.rkt"
                    define)
          [set k-set])
         racket/control)


(define stepping-frame%
  (class frame%
    (super-new)
    
    (field
      [k (λ () (void))]
      [btn (new button%
                [parent this]
                [label "Step"]
                [callback (λ (b e)
                            (k))])]
      [t (new pasteboard%)]
      [ch (make-channel)]
      [the-content (make-object string-snip% (format "~a" "123"))]
      [ec (new editor-canvas% [parent this] [editor t])])

    (define/public (one-step val cont)
      (send t delete the-content)
      (set! the-content (make-object string-snip% (format "~a" val)))
      (send t insert the-content)
      (set! k cont)
      (yield 'wait)
      (abort ))
    
    (send t insert the-content)
    
 ))


#;(define (init-step)
  (define f (new frame%
                 [label "Stepper"]
                 [width 400]
                 [height 300]))
  (define btn (new button%
                   [parent f]
                   [label "Step"]))
  (define t (new pasteboard%) )
  (define the-content (make-object string-snip% ""))
  (define ec (new editor-canvas% [parent f] [editor t]))
  (send t insert the-content)
  (send f show #t)
  f)

#;(define (stepping f text cont)
  )

(define (init-step)
  (define f (new stepping-frame%
                 [label "Stepper"]
                 [width 400]
                 [height 300]))
  (send f show #t)
  f)


(define the-frame (init-step))
(for/fold ([acc '()])
          ([x (in-list '(0 1 2 3))])
  (let ([acc-now (cons x acc)])
    (call/cc
     (λ (k) (send the-frame one-step acc-now k)))
  acc-now))
