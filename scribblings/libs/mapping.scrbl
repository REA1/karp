#lang scribble/manual

@title[#:tag "ch:lib-mapping"]{mapping}

@(require (for-label karp/lib/mapping)
          scribble-math)
@defmodule[karp/lib/mapping]

@defproc[(lookup [f mapping?] [k nay]) any]{
  Get the image of @racket[k] under the mapping @racket[f].
  The @racket[lookup] keyword can be omitted in the verifier definition,
  i.e., use @racket[(f k)] instead of @racket[(lookup f k)].
}

@defproc[(dom [f mapping?]) any]{
  Get the domain set of the mapping @racket[f].
}

@defform*[#:kind "type-descriptor / procedure"
          #:literals (~>)
          [(mapping #:from domain #:to codomain maybe-disjoint)
          (mapping [k ~> v] ...)]
          #:grammar ([maybe-disjoint code:blank #:disjoint])
          #:contracts ([domain (code:line value-descriptor? Set?)]
                      [codomain (code:line value-descriptor? Set?)])]{
 @itemize{
  @item{type-descriptor: @racket[#:disjoint] can only be used when the codomain is a
  family of sets, i.e., a set of sets. It requires the images of each pair of elements
  being disjoint.}
  
  @item{procedure: create a mapping with key-value pairs (@racket[k],@racket[v]) ... .

   @bold{NOT available inside verifier definitions}
  }
 }
}

@defmodule[karp/lib/mapping-reduction #:no-declare]


@defform[ #:link-target? #f
          #:literals (for ∈ ~>)
         (mapping x-in-X-to-img ...+)
          #:grammar ([x-in-X-to-img (code:line [x ∈ X] maybe-pred-x ~>) img-expr]
                     [maybe-pred-x (code:line where pred-x)])
          #:contracts ([X set?]
                       [pred-x boolean-expression?])]{
Create a mapping of the form
@$${
    m(x) = \begin{cases} f(x) & x \in X \text{ and } P(x) \\ \dots\end{cases},
}

where @${x} is @racket[X], @${f(x)} is @racket[img-expr] and @${P(x)} is @racket[pred-x].
If one elements appears multiple times in the definition, its element in the mapping is determined
by the last apperance of the @racket[x-in-X-to-img] sequence.

@defthing[curr mapping?]{
   @racket[curr] provides access the mapping object
   that has been constructed up to the point before @racket[curr]
   inside the mapping constructor.
}

}