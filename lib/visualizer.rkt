#lang racket

(require racket/draw
         pict
         racket/gui
         (except-in mrlib/graph dot-positioning)
         framework
         (only-in "../private/core-structures.rkt"
                  dp-set-members->list)
         (only-in "modified/dot.rkt" dot-positioning)
         "graph-base.rkt")

(provide visualize)

 (define vertex-snip%
    (class (graph-snip-mixin snip%)
      (inherit set-snipclass
               get-admin)
      (init-field k-v [size 20.0])
      
      (super-new)
      (set-snipclass vertex-snip-class)
      (send (get-the-snip-class-list) add vertex-snip-class)
      
      (define/override (get-extent dc x y	 	 	 	 
                                   [w #f]
                                   [h #f]
                                   [descent #f]
                                   [space #f]
                                   [lspace #f]
                                   [rspace #f])
        (define (maybe-set-box! b v) (when b (set-box! b v)))
        (maybe-set-box! w (+ 2.0 size))
        (maybe-set-box! h (+ 2.0 size))
        (maybe-set-box! descent 1.0)
        (maybe-set-box! space 1.0)
        (maybe-set-box! lspace 1.0)
        (maybe-set-box! rspace 1.0))
      
      (define/override (draw dc x y left top right bottom dx dy draw-caret)
        (define out (open-output-string))
        (print k-v out)
        (define label (get-output-string out))
        (define-values (w h d a) (send dc get-text-extent label))

        (define size-w-text (+ (max w h size) 5.0))
        
        (send dc draw-ellipse (+ x 1.0) (+ y 1.0) size size)
        (send dc draw-text label (+ x 2.0) (+ y 4.0)))
      
      (define/override (copy)
        (new vertex-snip% [size size]))
      
      (define/override (write f)
        (send f put size))
      
      ))
   
  (define vertex-snip-class%
    (class snip-class%
      (super-new)
      ))
   
  (define vertex-snip-class (new vertex-snip-class%))

(define karp-graph-frame%
  (class frame%
    (super-new)))

(define graph-pasteboard% 
  (class (graph-pasteboard-mixin pasteboard%)   
    (super-new)))


(define (visualize a-k-graph [title "Graph"])
  (define directed? (dp-graph-directed? a-k-graph))
  
  (define toplevel (instantiate karp-graph-frame% ()
                     (label title)
                     (width 600)
                     (height 400)))

  (define graph-pb
    (let ([pb (new graph-pasteboard%)])
      (send pb set-flip-labels? #f)
      pb))
  
  (define canvas (new editor-canvas% [parent toplevel] [editor graph-pb]))

  (define V-lst (dp-set-members->list (dp-graph-V a-k-graph)))

  (define vertex-snip%-lst
    (map (λ (a-karp-v)
           (new vertex-snip% (k-v a-karp-v))) V-lst))

  (map (λ (a-v) (send graph-pb insert a-v)) vertex-snip%-lst)

  (define link-created? (make-hash))
  (for* ([u vertex-snip%-lst]
         [v vertex-snip%-lst])
    (when (and (has-edge? (get-field k-v u) (get-field k-v v) a-k-graph)
               (or directed? (not (hash-ref! link-created? (cons u v) #f))))
      (hash-set! link-created? (cons u v) #t)
      (add-links u v)))
  
  (dot-positioning graph-pb dot-label #f directed?)
  (send graph-pb set-draw-arrow-heads? directed?)
  (send toplevel show #t))



