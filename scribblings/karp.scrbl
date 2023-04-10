#lang scribble/manual

@require[scribble-math]

@title[#:style (with-html5 manual-doc-style)]{Karp: A Language for NP Reductions}
@author{Chenhao Zhang}

@(require #;(for-label racket)
          scribble/racket)


@;@defmodulelang*[(karp/problem-definition karp/reduction)]

Karp is a domain specific language for writing reductions between NP
problems as programs  and random-testing their correctness.

This documentation gives a tutorial-style guide to programming in Karp,
followed by a description of its features and libraries. 
For details about the design rationale and the implementation of Karp, see
@hyperlink["https://doi.org/10.1145/3519939.3523732"]{"Karp: a language for NP reductions"}.

@(table-of-contents)

@include-section["quickstart/quickstart.scrbl"]
@include-section["problem-definition/problem-definition.scrbl"]
@include-section["reduction/reduction.scrbl"]
@include-section["libs/libs.scrbl"]
