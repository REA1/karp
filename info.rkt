#lang info
(define collection "karp")
(define deps '("base" "rosette"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"
		     "scribble-math"))
(define scribblings '(("scribblings/karp.scrbl" (multi-page))))
(define pkg-desc "Karp -- a language NP reductions")
(define version "0.9")
(define pkg-authors '(Chenhao Zhang))
