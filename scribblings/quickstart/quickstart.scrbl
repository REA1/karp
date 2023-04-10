#lang scribble/manual

@(require (for-label karp/problem-definition
                     karp/reduction
                     karp/lib/graph
                     karp/lib/cnf)
          scribble/example
          scribble-math)

@(define 3-SAT @${\rm 3\text{-}S{\small AT}})
@(define I-SET @${\rm I{\small NDEPENDENT}\text{-}S{\small ET}})

@title[#:tag "ch:quickstart" #:style (with-html5
manual-doc-style)]{Getting Started with Karp, by Example}

We start with a preliminary discussion of NP problems and reductions. 

In Karp, reductions concern decision problems, that is, 
problems that have a "yes" or "no" answers. Two classic decision problems
are @3-SAT and @|I-SET|. The first asks whether a 3-CNF formula is
satisfiable. The second asks whether an undirected graph has at least
@${k} nodes that are not neighbors with each other. 

We say that an instance of a decision problem is a yes-instance if there exists a
certificate that verifies the ``yes'' answer. For instance, for an instance of
@3-SAT, that is a specifc 3-CNF formula, a certificate is a satisfying assignment
that is a map from the variables of the formula to the booleans that makes
the formula true. Similarly, for an instance
of @I-SET, that is an undirected graph and a natural number @${k}, a
certificate is a subset of the nodes of the graph that has at least size
@${k} and the nodes it contains are not neighbors. 

If an instance has no certificate, then it is a no-instance. 

We say a decision problem is in @${NP} if there exist short certificates for
all yes-instances, that is, there are ceritificates that
can verify the ``yes'' answer in poly-time with respect to the size of the
instance. Given a candidate certifcate for an instance, it is much easier
to verify the ``yes'' or ``no'' answer than solving the actual instance.
Hence, this definition admits both problems that we know how to solve
easily, that is in poly-time, and hard problems for which we do not have
poly-time algoritms.  

A principled way to show that an @${NP} decision problem, such as
@I-SET,  is hard is with a correct reduction from a well-known @${NP}-hard
problem, such as @3-SAT, to the problem whose ``hardness'' we investigate. 
A reduction is a function that given an instance of its from-problem
constructs an instance of its to-problem. A @bold{correct} reduction is a
@bold{poly-time} reduction that 
@bold{maps yes-instances to yes-instance and no-instances to
no-instances}. For instance, a correct reduction from @3-SAT to @I-SET maps
(i) every 3-CNF formula with a satisfying assignment to an undirected graph
that has an independent size of at least size @${k}, for some @${k}; and
(ii) every 3-CNF that does not have a satisfying assignemnt to an an undirected graph
that has no independent size of at least size @${k}, for some @${k};

@section{The Structure of Reductions in Karp}

A reduction in Karp from decision problem @racketid[X] to decision
problem @racketid[Y] consists of three main pieces:
@itemize{
  @item{The two @italic{problem definition}s of @racketid[X] and
  @racketid[Y].}
  @item{The @italic{forward instance construction}, that is, the reduction
  itself which given an instance of  @racketid[X] constructs
  an instance of @racketid[Y].}}

In addition to these three pieces, for each reduction, Karp requires the
definition of two additional
functions that play the role of a proof argument about the correctness of 
the reduction:

@itemize{
  @item{The @italic{forward certificate construction} consumes 
  @racketid[x], a yes-instance of @racketid[X], and a certificate
  for @racketid[x], and produces a certificate for @racketid[y], the 
  result of applying the forward instance construction from @racketid[X] to
  @racketid[Y] on @racketid[x].}
   @item{The @italic{backward certificate construction} consumes 
  @racketid[x], a yes-instance of @racketid[X], and a certificate
  for @racketid[y], the 
  result of applying the forward instance construction from @racketid[X] to
  @racketid[Y] on @racketid[x], and produces a certificate for @racketid[y].}}

In essence, if these two functions succeed in translating a certificate for
any @racketid[x] to a certificate for the corresponding @racketid[y] and back,
the forward instance construction is correct: it translates yes(no)-instances
of @racketid[X] to yes(no)-instances of @racketid[Y].

In the remainder of this section, we use the reduction from @3-SAT to @I-SET 
to demonstrate concretely the five pieces of  a reduction
in Karp.


@section{Problem Definitions}



Each problem definition is written as a separate module of the dedicated
language @racket[karp/problem-definition].

The problem definition of @3-SAT is given below:
@codeblock[
   #:indent 0
  "#lang karp/problem-definition

  ; importing the karp cnf and mapping libraries
  (require karp/lib/cnf
           karp/lib/mapping)

  ; problem shape
  (decision-problem
            #:name 3sat
            #:instance ([φ is-a (cnf #:arity 3)])
            #:certificate (mapping #:from (variables-of φ)
                                   #:to (the-set-of boolean)))

 ; verifier definition
 (define-3sat-verifier a-inst c^3sat
   (∀ [C ∈ (clauses-of (φ a-inst))]
      (∃ [l ∈ (literals-of C)]
         (or (and
              (positive-literal? l) (lookup c^3sat (underlying-var l)))
             (and
              (negative-literal? l) (not (lookup c^3sat (underlying-var l))))))))"
 ]
The problem definition has two parts:
@itemlist[#:style 'ordered
          @item{Problem shape: The definition form
          @racket[decision-problem] gives a name to the defined problem,
          and specifies the shape of its
          instances and certificates. For
          @3-SAT, an instance is a 3-CNF formula @racketid[φ], 
          and a certificate a
          mapping from the variables of @racketid[φ] to the set of booleans.}
          @item{Verifier definition: the definition of the problem shape
          generates a form for defining  the certificate verifier of
          problem, that is a predicates that takes an instance and an alleged
           certificate, and checks if the alleged certificate 
           is indeed a certificate of the
           given instance. In the running example,
           the @racketid[define-3sat-verifier] form checks if the given
           assignment @racketid[c^3sat] makes true at least one literal
           @racketid[l] of each clause @racketid[C] of the given instance
           @racketid[a-inst].}]

After the problem @racketid[3sat] is defined, the constructors and the
certificate solver of @racketid[3sat] instances are enabled: 
@codeblock[
 #:keep-lang-line? #f
 "#lang karp/problem-definition
 (define foo (create-3sat-instance
     ([φ
       (cnf ('x1 ∨ 'x2 ∨ 'x3)
            ((¬'x1) ∨ (¬'x2) ∨ (¬'x3))
            ((¬'x1) ∨ (¬'x2) ∨ 'x3))])))
 (define foo-cert (mapping ('x1 ~> #f) ('x2 ~> #t) ('x3 ~> #f)))
 (3sat-verifier foo foo-cert) ;#t
 (define foo-non-cert (mapping ('x1 ~> #t) ('x2 ~> #t) ('x3 ~> #t)))
 (3sat-verifier foo foo-cert) ;#f
 (define foo-cert2 (3sat-solver foo))
 (3sat-verifier foo foo-cert2) ;#t"
]


In a similar manner, the @I-SET problem can be defined as follows:
@codeblock[
 #:indent 0
 "#lang karp/problem-definition

(require karp/lib/graph)

; problem structure definition
(decision-problem
          #:name iset
          #:instance ([G is-a (graph #:undirected)]
                      [k is-a natural])
          #:certificate (subset-of (vertices-of G)))

 ; verifier definition
 (define-iset-verifier a-inst c^iset
  (and
   (>= (set-size c^iset) (k a-inst))
   (∀ [u ∈ c^iset]
     (∀ [v ∈ (neighbors (G a-inst) u)]
       (set-∉ v c^iset)))))"
 ]

The definition of independent set uses Karp's graph
library. A graph can be created as follows:
@codeblock[
 #:keep-lang-line? #f
 "#lang karp/problem-definition
 (define V1 (set 'x1 'x2 'x3 'x4))
 (define E1 (set ('x1 . -e- . 'x2)
                 ('x1 . -e- . 'x3)
                 ('x3 . -e- . 'x4)
                 ('x2 . -e- . 'x3)))
 (define G1 (create-graph V1 E1))
 "
]
We can then create an @racket[iset] instance from the graph
and play around with it:
@codeblock[
 #:keep-lang-line? #f
 "#lang karp/problem-definition
 (define/iset-instance iset-inst1 ([G G1] [k 2]))
 (iset-verifier iset-inst1 (set 'x1 'x4)) #; #t
 (iset-verifier iset-inst1 (set 'x1 'x3)) #; #f
 (define c^iset1 (iset-solver iset-inst1))
 (iset-verifier iset-inst1 c^iset1) #; #t
 "
]

@section{Reduction}
The remaining part of the reduction in Karp is defined using the sublangauge
@racketmod[karp/reduction]
The three constructions are defined using @racket[define-forward-instance-construction],
@racket[define-forward-certificate-construction] and @racket[define-backward-certificate-construction]
respectively.
                                                             
@codeblock[
 #:indent 0
 "#lang karp/reduction
 ; importing the problem definitions and the libraries.
 (require (union-in \"3sat.karp\" \"iset.karp\")
          karp/lib/cnf
          karp/lib/graph
          karp/lib/mapping-reduction)"
]

Recall that in a correct reduction from @3-SAT to @I-SET
constructs an @I-SET instance from a given @3-SAT instance in the following steps:

@itemlist[ #:style 'ordered
@item{Create a vertex for each literal in each clause of the CNF of the @3-SAT instance:
@image["scribblings/figures/1.png"
       #:scale 0.2]{V}}

@item{Add the set of edges @${E1} that connects the vertices that correspond to
literals that are negation of each other:
@image["scribblings/figures/2.png"
       #:scale 0.2]}

@item{Add the set of edges @${E2} that connects the vertices that correspond to
literals in the same clause.
@image["scribblings/figures/3.png"
       #:scale 0.2]}

@item{Finally, by putting the graph together and set the threshold @${k} to be the number
of clauses, we get the @I-SET instance.}
]

The Karp code for the procedure is shown below:
@codeblock[
 "(define-forward-instance-construction
  #:from 3sat #:to iset
  (3sat->iset-v1 a-3sat-inst)

  (define Cs (clauses-of (φ a-3sat-inst)))
  ; creating the node for the graph
  (define V (for/set {(el l i) for [l ∈ C] for [(C #:index i) ∈ Cs]}))
  ; creating the set E1 for the graph
  (define E1
    (for/set {((el l1 i) . -e- . (el l2 j))
              for [l1 ∈ (literals-of C1)] for [l2 ∈ (literals-of C2)]
              for [(C1 #:index i) ∈ Cs] for [(C2 #:index j) ∈ Cs]
              if (literal-neg-of? l1 l2)}))
  ; creating the set E2 for the graph
  (define E2
    (for/set {((el (fst p) i) . -e- . (el (snd p) i))
              for [p ∈ (all-pairs-in (literals-of C))]
              for [(C #:index i) ∈ Cs]}))

  ; commenting out the E2 to introduce a mistake
  (create-iset-instance ([G (create-graph V (set-∪ E1 E2))]
                         [k (set-size Cs)])))"]
The code shown above defines an instance transformation function with name
@racket[3sat->iset-v1] which takes one arguement @racket[a-3sat-inst]
and produces an @racket[iset] instance.

In the definition of @racketid[E1], we create each vertices
as an abstract element @racketid[el] with first subscript being
the literal itself and the second subscript being the index
of the clause in the CNF that literal comes from.

@racket[[(C #:index i) ∈ Cs]] binds the index of the current element @racket[C]
in question @racket[C] in set @racket[Cs] to @racket[i].

@racket[((el l1 i) . -e- . (el l2 j))] creates an (undirected) edge with endpoints 
@racket[(el l1 i)] and @racket[(el l2 j)].

@subsection{Forward Certificate Construction}

The forward certificate construction maps a certificate of the from-problem
instance to a certificate of the to-problem. It serves as a proof that
a no-instance is always transformed to a no-instance.

To construct a certificate of @I-SET from a certificate of @3-SAT,
we find one literal in each clause of the CNF that is satisfied
under the assignment and pick the vertices
corresponding to these literals to form the certificate.
@image["scribblings/figures/4.png"
       #:scale 0.2]

The Karp code is shown below:
@codeblock[
 "(define-forward-certificate-construction
  #:from 3sat #:to iset
  (3sat->iset->>-cert-v1 s->t-constr a-3sat-inst c^sat)

  ; getting the set of vertices from the assignment
  (for/set
     {(el
        (find-one [l ∈ C] s.t.
          (or
            (and (positive-literal? l)
                 (lookup c^sat (underlying-var l)))
            (and (negative-literal? l)
                 (not (lookup c^sat (underlying-var l))))))
        i)
       for [(C #:index i) in (φ a-3sat-inst)]}))"]
The code snippet defines a transformation function with name
@racket[3sat->iset->>-cert-v1] that expects three arguments:
@itemlist{@item{an instance transformation function @racket[s->t-constr]}@item{a @racket[3sat] instance @racket[a-3sat-inst]}@item{a @racket[3sat] certificate @racket[c^sat],
  which is a mapping from the variables of @racket[a-3sat-inst] to Booleans}}
 It returns an @racket[iset] certificate, which is a subset of vertices.

@subsection{Backward Certificate Construction}

The backward certificate construction maps a certificate of the to-problem
instance back to a certificate of the from-problem instance. It serves as a proof that
a yes-instance is always transformed to a yes-instance.

To construct a @3-SAT certificate from an @I-SET certificate:
We first find those variables that should be assigned to true.
Each of these variable must be the underlying variable of some
positive literal, the vertex correponding to which is
in the independent set. We then create a mapping with these
variables mapped to true and all other variables mapped to false.
(The illustration is the same as the previous one)

The procedure is decribed in Karp as follows:
@codeblock[
"(define-backward-certificate-construction
  #:from 3sat #:to iset 
  (3sat->iset-<<-cert-v1 s->t-constr a-3sat-inst c^iset)

  (define X (variables-of (φ a-3sat-inst)))
  ; mapping back from vertices to assignments
  (define X-True
    (for/set {x for [x ∈ X]
                if (∃ [v in c^iset]
                      (and
                       (positive-literal? (_1s v))
                       (equal? (underlying-var (_1s v)) x)))}))
  (mapping
   [x ∈ X-True] ~> #t
   [x ∈ (set-minus X X-True)] ~> #f))"]

To extract the corresponding literal from the vertex, we
use @racket[_1s] to get the first subscript of the vertex,
which is an abstract element as we defined in the instance construction.

@subsection{Testing Reductions}
We now have all parts of a runnable and testable reduction ready, we can
random test it with @racket[check-reduction] by supplying the three transformation
functions we just defined.
@racketblock[(check-reduction #:from 3sat #:to iset
                 3sat->iset-v1 3sat->iset->>-cert-v1 3sat->iset-<<-cert-v1)]

To see how a buggy reduction can be caught by the random testing,
omitting the @racket[E2] in the instance construction and rerun
@racket[check-reduction]. @racket[(get-counterexample)] can be used
to access the @3-SAT instance found as counterexample in the latest
run of the @racket[check-reduction]. To reproduce the testing results
to help debugging, a random seed can be specified by adding an extra
option @racket[#:random-seed] to @racket[check-reduction].
