#lang scribble/manual

@require[scribble-math]

@title[#:style (with-html5 manual-doc-style)]{Karp: A Language for NP Reductions}
@author{Chenhao Zhang}

@(require #;(for-label racket)
          scribble/racket)


@;@defmodulelang*[(karp/problem-definition karp/reduction)]

Karp is a domain specific language for writing reductions between NP problems and random-testing
their correctness.

More details about the design and implementation of Karp can be found in the PLDI'2022 research paper
@hyperlink["https://doi.org/10.1145/3519939.3523732"]{"Karp: a language for NP reductions"}.

@(table-of-contents)

@include-section["quickstart/quickstart.scrbl"]
@include-section["problem-definition/problem-definition.scrbl"]
@include-section["reduction/reduction.scrbl"]
@include-section["libs/libs.scrbl"]