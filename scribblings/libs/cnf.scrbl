#lang scribble/manual

@title[#:tag "ch:lib-cnf"]{cnf}

@(require (for-label karp/lib/cnf))
@defmodule[karp/lib/cnf]

Boolean Formulas in Conjunctive Normal Form

@defform*[#:kind "type-descriptor / syntax"
          #:literals (∨ ¬)
         ((cnf #:arity arity)
          (cnf clause ...))
         #:grammar ([clause (literal-first literal-next ...)]
                    [literal-first literal]
                    [literal-next (code:line ∨ literal)]
                    [literal variable (¬ variable)])
         #:contracts ([arity natural?]
                      [variable symbol?])]{
 @itemize{
  @item{type-descriptor:}
  @item{procedure: create a cnf with clauses.

   @bold{NOT available inside verifier definitions}                                        
  }
 }
}

@defform*[#:kind "value-descriptor / procedure"
           ((variables-of a-cnf)
            (variables-of c))
          #:contracts ([a-cnf (code:line value-descriptor? CNF?)]
                       [c (code:line cnf? clause?)])]{
  Get the set of variables of the CNF or clause @racket[c] when used outside
  @racket[decision-problem].
}

@defproc[(literals-of [c clause?]) (setof literal?)]{
 Get the set of literals of clause @racket[c].
}

@defproc[(neg [l (code:line literal? _or symbol?)]) literal?]{
 Get the negation of a literal @racket[l]. When @racket[l] is a variable
 (i.e., symbol), a negative literal with underlying variable @racket[l] is
 produced.
}

@defproc[(underlying-var [l literal?]) symbol?]{
 Get the underlying variable of literal @racket[l].
}

@defproc[(positive-literal? [l literal?]) boolean?]{
 Test if literal @racket[l] is a positive literal.
}

@defproc[(negative-literal? [l literal?]) boolean?]{
 Test if literal @racket[l] is a negative literal.
}

@defproc[(literal-neg-of? [l1 literal?] [l2 literal?]) boolean?]{
 Test if literal @racket[l1] is the negation of @racket[l2].
}

@defproc[(same-variable? [l1 literal?] [l2 literal?]) boolean?]{
 Test if literals @racket[l1] and @racket[l2] have the same variable.
}

@defproc[(clauses-of [c cnf?]) (setof clauses)]{
 Get the set of all clauses of CNF @racket[c].
}