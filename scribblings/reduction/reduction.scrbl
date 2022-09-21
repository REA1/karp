#lang scribble/manual

@title[#:tag "ch:reduction"]{Reduction}

@(require (for-label karp/problem-definition
                     karp/reduction)
          scribble-math)

@defmodulelang[karp/reduction]

@defform[(define-forward-instance-construction
           #:from from-name #:to to-name
           id inst-arg
           body ...+)]{

 Define a forward instance construciton function from decision
 problem @racket[from-name] to decision problem @racket[to-name]
 with name @racket[id]. The function takes one @racket[from-name]-instance
 as its arugment and produces one @racket[to-name]-instance as its output.

 The final expression of the body is expected to evaluate to an
 @racket[to-name]-instance.
}

@defform[(define-forward-certificate-construction
           #:from from-name #:to to-name
           id f->t-construction-arg inst-arg cert-arg
           body ...+)]{
 Define a forward certificate construciton function from decision
 problem @racket[from-name] to decision problem @racket[to-name]
 with name @racket[id]. The function takes one @racket[from-name]-instance
 and a @racket[from-name]-certificate of the instance
 as its arugments and produces one @racket[to-name]-certificate as its output.

 The final expression of the body is expected to evaluate to an
 @racket[to-name]-certificate.
}

@defform[(define-backward-certificate-construction
           #:from from-name #:to to-name
           id f->t-construction-arg inst-arg cert-arg
           body ...+)]{
 Define a forward certificate construciton function from decision
 problem @racket[from-name] to decision problem @racket[to-name]
 with name @racket[id]. The function takes one @racket[from-name]-instance
 and a @racket[to-name]-certificate of the instance
 as its arugments and produces one @racket[from-name]-certificate as its output.

 The final expression of the body is expected to evaluate to an
 @racket[from-name]-certificate.
 
 @defthing[target-inst instance?]{
  Can only be used inside the body of @racket[define-forward-certificate-construction] and
  @racket[define-forward-certificate-construction].

  Use @racket[target-inst] to
  access the to-problem instance constructed from the current from-problem instance through
  the supplied forward instance construction.
 }
}

@defform[(define id expr)]{
   Define @racket[id] as the result of @racket[expr].
}

@defform[(check-reduction #:from from-name #:to to-name
                          maybe-from-generator maybe-n-test maybe-random-seed
                          f->t-instance-construction
                          f->t-certificiate-construction
                          t->f-certificate-construction)
         #:grammar ([maybe-from-generator code:blank (code:line #:from-generator generator)]
                    [maybe-n-test code:blank (code:line #:n-test n-test)]
                    [maybe-random-seed code:blank (code:line #:random-seed random-seed)])
         #:contracts ([from-name decision-problem]
                      [to-name decision-problem]
                      [n-test natural?]
                      [random-seed natural?])]{
Run random testing on the given reduction.

The @racket[f->t-instance-construction],
@racket[f->t-certificiate-construction] and @racket[t->f-certificate-construction]
arguments should be construction functions defined with
@racket[define-forward-instance-construction], @racket[define-forward-certificate-construction]
and @racket[define-backward-certificate-construction] respectively.
}

@defform[(get-counterexample)]{
  Access counterexample instance of the from-problem found by the last run of @racket[check-reduction].
}

@defform[(union-in file-1 file-2)]{
  Import the decision problem definitions from @racket[file-1] and @racket[file-2]. @racket[union-in]
takes care of the fields that share the same name across the two decision problems.
}

@section{Additional Operations}

@bold{The additional operations described in this section are NOT available in verifier definitions}.

@defform[(if cond-expr then-expr else-expr)]{
    @$${\begin{cases}
           a & p \\
           b & o.w.
        \end{cases}}
   where @${a} is @racket[then-expr], @${b} is @racket[else-expr], and
 @${p} is @racket[cond-expr]
}

@defform[#:literals (for ∈ if)
         (for/set { el-expr element-in-set ...+ maybe-cond })
         #:grammar ([element-in-set (code:line for [var ∈ X])]
                    [var x (code:line (x #:index i))]
                    [maybe-cond (code:line if cond-expr)])
         #:contracts ([X set?]
                      [cond-expr boolean-expression?])]{
Create a set with representative element @racket[el-expr] going over all element @racket[x]
in @racket[X] ... satisfying the @racket[cond-expr], i.e.,
@$${ \{ f(x,y,\dots) \mid x \in X(y,\dots), y \in Y(\dots),P(x,y,\dots) \} }
}

When the form @racket[[(x #:index i) ∈ X]] is used, @racket[i] is bound to the index
of @racket[x] in set @racket[X].

@defproc[(corr [x any]) any]{
 If @racket[x] is an element of a set created with @racket[for/set],
 @racket[(corr x)] produces one element that @racket[x] is created from.
}

@defform[#:literals (for ∈ s.t.)
         (find-one [var ∈ X] maybe-cond)
         #:grammar ([var x (code:line (x #:index i))]
                    [maybe-cond (code:line s.t. cond-expr)])
         #:contracts ([X set?]
                      [cond-expr boolean-expression?])]{
 Get an (arbitary) element from set @racket[X] that satisfies the condition. An error
will be triggered if no such elemenet exists.

 When the form @racket[[(x #:index i) ∈ X]] is used,
 @racket[i] is bound to the index of @racket[x] in set @racket[X].
}

@defform[#:literals (for ∈ s.t.)
         (argmax x-expr [x ∈ X] maybe-cond)
         #:grammar ([maybe-cond (code:line s.t. cond-expr)])
         #:contracts ([X set?]
                      [x-expr number-expression?]
                      [cond-expr boolean-expression?])]{
}

@defform[#:literals (for ∈ s.t.)
         (argmin x-expr [x ∈ X] maybe-cond)
         #:grammar ([maybe-cond (code:line s.t. cond-expr)])
         #:contracts ([X set?]
                      [x-expr number-expression?]
                      [cond-expr boolean-expression?])]{
}

@defform[(all-pairs-in X maybe-ordered)
         #:grammar ([maybe-ordered code:blank (code:line #:ordered)])]{
 Produce a set containing all pairs (2-tuple) of elements in set @racket[X].                                                              
}

@defform[(all-triplets-in X maybe-ordered)
         #:grammar ([maybe-ordered code:blank (code:line #:ordered)])]{
 Produce a set containing all triplets (3-tuple) of elements in set @racket[X].                                                              
}

@defproc[(el [subscript any] ...)
         abstract-element]{
 An abstract element with subscripts @racket[subscript] ... .
}

@defproc[(_1s [e el?]) any]{
 Get the first subscript of @racket[e] ... .
}

@defproc[(_2s [e el?]) any]{
 Get the second subscript of @racket[e] ... .
}

@defproc[(_3s [e el?]) any]{
 Get the third subscript of @racket[e] ... .
}

@defproc[(_ks [e el?] [k positive-integer?]) any]{
 Get the k-th subscript of @racket[e] ... .
}

@defproc[(index-in [e any] [S set?]) natural?]{
 Get the index of the @racket[e] in set @racket[S].
}

@defproc[(element-of-index [i natural?] [S set?]) any]{
 Get the element in set @racket[S] of index @racket[i].
}

@defproc[(ints-from-to [from (code:line natural? polynomial-size?)]
                       [to (code:line natural? polynomial-size?)])
         (setof natural?)]{
 Produce the set of integers from @racket[from] to @racket[to] inclusive of the endpoints. The endpoints must
 be within polynomial of the input size.
}