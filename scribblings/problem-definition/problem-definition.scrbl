#lang scribble/manual

@(require (for-label karp/problem-definition)
          scribble-math)

@title[#:tag "ch:problem-definition" #:style (with-html5 manual-doc-style)]{Problem Definition}

@defmodulelang[karp/problem-definition]


@defform[#:literals (is-a)
         (decision-problem #:name name
                            #:instance ([field-name is-a type-descriptor] ...+)
                            #:certificate type-descriptor)]{
  Defines a decision problem @racket[name] with its instance
  and certificate structures.

  Defining a decision problem @racket[x]'s structure enables 3 other language constructs:
  @itemize{
    @item{The constructor for @racket[x]-instance:
         @specform[(create-x-instance ([field-name expr] ...))]
         @specform[(define/x-instance id ([field-name expr] ...))]
         The order of @racket[field-name]s does not need to match the order they are defined
         in @racket[decision-problem].
    }
    @item{
         The field accessors for each field of an instance, which are just the @racket[field-name]s.
    }
    @item{The @racket[define-x-verifier] definition form to define the verifier of problem @racket[x].
      @specform[(define-x-verifier inst-arg cert-arg
                  body ...+)]
    The id of the verifier of problem @racket[x] is @racket[x-verifier]. It also enables the solver
    function @racket[x-solver], which can be called by the user when debugging the reduction.
    @racket[x-solver] takes an @racket[x]-instance and produce a certificate of the instance or reports
    no solution.
    }
 }
}


@section{Core Datatype}

@defproc[(equal? [a any] [b any]) boolean]{
   Test if @racket[a] and @racket[b] are equal.
}

@subsection{Atomic Type}

@defform[#:kind "type-descriptor"
         (natural maybe-length)
         #:grammar ([maybe-length code:blank #:cardinal #:numeric])]{
 @itemize{
          
  @item{@racket[#:cardinal] specifies that the value is encoded in unary. Hence, the numeric value
   of the number is polynomial to the input size.}
  
  @item{@racket[#:numeric] specifies that the value is encoded in binary.
  Hence, the numeric value of the number is exponential to the the input size. To guarantee a reduction
  runs in polynomial time to the input size, certain operations are not allowed on such numbers.}
  
 }

 When not specified, @racket[#:cardinal] is assumed by default.
}

@defform[#:kind "type-descriptor"
         (boolean)]{}

@defform[#:kind "type-descriptor"
         (symbol)]{}

@subsection{Set}

@defform*[#:kind "type-descriptor / procedure"
         [(set maybe-element-type maybe-size)
          (set e ...)]
         #:grammar ([maybe-element-type code:blank
                     (code:line #:of-type element-type)]
                    [maybe-size code:blank
                     (code:line #:size size)])
         #:contracts ([element-type type-descriptor?]
                      [size (code:line value-descriptor? Natural?)])]{
 @itemize{
  @item{type-descriptor: When @racket[maybe-element-type] is not specified, there is no restriction
  on the element type of the set.}
  @item{procedure: create a set with elements @racket[e] ... .
                                             
   @bold{NOT available inside verifier definitions}
  }
 }
}

@defform[#:kind "type-descriptor"
         (subset-of superset maybe-size)
         #:grammar ([maybe-size code:blank
                     (code:line #:size natural-number)
                     (code:line #:size value-descriptor)])
         #:contracts ([superset (code:line value-descriptor? Set?)])]{}

@defform[#:kind "type-descriptor"
         (element-of a-set)
         #:contracts ([a-set (code:line value-descriptor? Set?)])]{}

@defform[#:kind "value-descriptor"
         (the-set-of a-type)
         #:contracts ([a-type type-descriptor?])]{
  This value descriptor gives the abstract set consisting of all elements of given type.
}

@defproc[(set-∈ [e any] [S set?])
         boolean?]{Test if @racket[e] is in set @racket[S].}

@defproc[(set-∉ [e any] [S set?])
         boolean?]{Test if @racket[e] is NOT in set @racket[S].}

@defproc[(set-size [S set?])
         natural?]{Get the size (cardinality) of set @racket[S], i.e.,
@${|S|} where @${S} is @racket[S]}

@defproc[(set-∩ [S set?] ...+)
         set?]{Get the intersection of the sets @racket[S] ... .}

@defproc[(set-∪ [S set?] ...+)
         set?]{Get the intersection of two sets @racket[S] ... .}

@defproc[(set-minus [S1 set?] [S2 set?])
         set?]{Get a set consisting of all elements in @racket[S1] but not @racket[S2], i.e.
@${S_1 \setminus S_2} where @${S_1, S_2} are @racket[S1],@racket[S2] respectively.}

@defform[#:literals (∈)
         (∀ [x ∈ X] pred-x)
         #:contracts ([X set?]
                      [pred-x boolean-expression?])]{
 Universial quantifier expression over the set @racket[X].
 Test if all element @racket[x] in @racket[X] satisfy @racket[pred-x].                                           
}

@defform[#:literals (∈)
         (∃ [x ∈ X] pred-x)
         #:contracts ([X set?]
                      [pred-x boolean-expression?])]{
 Existential quantifier expression over the set @racket[X].
 Test if there exists some element @racket[x] of @racket[X] satisfies @racket[pred-x].
}

@defform[#:literals (∈)
         (∃<=1 [x ∈ X] pred-x)
         #:contracts ([X set?]
                      [pred-x boolean-expression?])]{
Test if at most 1 element @racket[x] in @racket[X] satisfies @racket[pred-x].
}

@defform[#:literals (∈)
         (∃=1 [x ∈ X] pred-x)
         #:contracts ([X set?]
                      [pred-x boolean-expression?])]{
Test if exactly 1 element @racket[x] in @racket[X] satisfies @racket[pred-x].
}

@defform[#:literals (for ∈ if)
         (sum val-x for [x ∈ X] maybe-condition)
         #:grammar ([maybe-condition
                     code:blank
                     (code:line if pred-x)])
         #:contracts ([X set?]
                      [val-x interger-expression?]
                      [pred-x boolean-expression?])]{
}
Calculate
@$${\sum_{x \in X , P(x)}f(x)}
where the expression @racket[val-x] of @racket[x] is @${f(x)}
and the expression @racket[pred-x] of @racket[x] is @${P(x)}.

@defform[#:literals (for ∈ if)
         (max val-x for [x ∈ X] maybe-condition)
         #:grammar ([maybe-condition
                     code:blank
                     (code:line if pred-x)])
         #:contracts ([X set?]
                      [val-x interger-expression?]
                      [pred-x boolean-expression?])]{
}
Calculate
@$${\max_{x \in X , P(x)}\{f(x)\}}
where the expression @racket[val-x] of @racket[x] is @${f(x)}
and the expression @racket[pred-x] of @racket[x] is @${P(x)}.

@defform[#:literals (for ∈ if)
         (min val-x for [x ∈ X] maybe-condition)
         #:grammar ([maybe-condition
                     code:blank
                     (code:line if pred-x)])
         #:contracts ([X set?]
                      [val-x interger-expression?]
                      [pred-x boolean-expression?])]{
}

Calculate
@$${\min_{x \in X , P(x)}\{f(x)\}}
where the expression @racket[val-x] of @racket[x] is @${f(x)}
and the expression @racket[pred-x] of @racket[x] is @${P(x)}.

@subsection{Tuple}

@defform[#:kind "type-descriptor"
         (tuple field-type ...+)
         #:grammar ([field-type (code:line #:field-type type)])
         #:contracts ([type (code:line type-descriptor?)])]{
A tuple is a (ordered) sequence with fixed length.
}

@defform[#:kind "value-descriptor"
         (product-of a-set ...+)
         #:contracts ([a-set (code:line value-descriptor? Set?)])]{
 The value specified by this value descriptor is the set consisting of all tuples with
 the element on each component coming from @racket[a-set] ... in order.
}

@defproc[(tpl [e any] ...+) tuple?]{
  Create a tuple with components @racket[e] ... .

  @bold{NOT available in verifier definitions}
}

@defproc[(fst [t tuple?]) any]{
  Get the first component of tuple @racket[t].
}

@defproc[(snd [t tuple?]) any]{
  Get the second component of tuple @racket[t].
}

@defproc[(trd [t tuple?]) any]{
  Get the third component of tuple @racket[t].
}

@defproc[(frh [t tuple?]) any]{
  Get the forth component of tuple @racket[t].
}

@defproc[(ffh [t tuple?]) any]{
  Get the fifth component of tuple @racket[t].
}

@defproc[(n-th [t tuple?] [n natural?]) any]{
  Get the @racket[n]-th component of tuple @racket[t].
}
