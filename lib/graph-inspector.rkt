#lang racket

(require racket/draw
         pict
         racket/gui
         (except-in mrlib/graph dot-positioning)
         framework
         (only-in "../private/core-structures.rkt"
                  dp-set-members->list
                  [set dp-set])
         (only-in "modified/dot.rkt" dot-positioning)
         "graph.rkt")

(provide visualize render-graph/snip)

(define vertex-snip-class%
  (class snip-class%
    (super-new)
    ))
   
(define vertex-snip-class (new vertex-snip-class%))

(define vertex-snip%
  (class (graph-snip-mixin snip%)
    (inherit set-snipclass
             get-admin)
    (init-field k-v size)
      
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
      
    #;(define/override (copy)
      (new vertex-snip% [size size]))
      
    (define/override (write f)
      (send f put size))
      
    ))

(define graph-pasteboard% 
  (class (graph-pasteboard-mixin pasteboard%)   
    (super-new)))

; a-k-graph -- a karp graph
(define (to-graph-pb a-k-graph [v-size 20.0])
  (define directed? (dp-graph-directed? a-k-graph))

  (define graph-pb
    (let ([pb (new graph-pasteboard%)])
      (send pb set-flip-labels? #f)
      pb))

  (define V-lst (dp-set-members->list (dp-graph-V a-k-graph)))

  (define vertex-snip%-lst
    (map (λ (a-karp-v)
           (new vertex-snip% [k-v a-karp-v] [size v-size] )) V-lst))

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
  
  graph-pb)


(define (visualize a-k-graph [title "Graph"])
  
  (define toplevel (instantiate frame% ()
                     (label title)
                     (width 600)
                     (height 400)))

  (define the-graph-pb (to-graph-pb a-k-graph))
  
  (define canvas (new editor-canvas% [parent toplevel] [editor the-graph-pb])) 
  (send toplevel show #t))


; See rosette/value-browser.rkt

(define snip-class (new snip-class%))
(define graph-editor-snip%
  (class editor-snip%
    (init-field graph-pb)
  
    (super-new [editor graph-pb] [min-height 200] [min-width 800])

    (define/override (copy) (new graph-editor-snip% [graph-pb graph-pb]))
    (define/override (write _) (void))
    (inherit set-snipclass)
    (set-snipclass snip-class)))

(define (render-graph/snip a-k-graph)

  (define the-graph-pb (to-graph-pb a-k-graph 15.0))

  (new graph-editor-snip% [graph-pb the-graph-pb]))


#;(create-graph-from-edges (set ('a . -e- . 'b)))