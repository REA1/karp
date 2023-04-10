#lang scribble/manual

@title[#:tag "ch:lib-graph"]{graph}

@(require (for-label karp/problem-definition
                     karp/lib/graph))
@defmodule[karp/lib/graph]

@defform[#:kind "type-descriptor"
         (graph directedness)
         #:grammar ([directedness #:undirected
                                  #:directed])]{}

@defform[#:kind "type-descriptor"
         (subgraph-of a-graph)
         #:contracts ([a-graph (code:line value-descriptor? Graph?)])]{}

@defform*[#:kind "value-descriptor / procedure"
           ((edges-of a-graph)
            (edges-of g))
          #:contracts ([a-graph (code:line value-descriptor? Graph?)]
                       [g graph?])]{
  Get the set of edges of the graph @racket[g] when used outside
  @racket[decision-problem].
}

@defform*[#:kind "value-descriptor / procedure"
           ((vertices-of a-graph)
            (vertices-of g))
          #:contracts ([a-graph (code:line value-descriptor? Graph?)]
                       [g graph?])]{
   Get the set of vertices of the graph @racket[g] when used outside
  @racket[decision-problem].                                          
   @;{@itemize{
  @item{In @racket[decision-problem]: a value-descriptor }
  @item{Regular function: Get the }
}}
}

@defproc[(endpoints [e edge?]) (setof? any)]{
 Get the set of endpoints of a given edge @racket[e].
}

@defproc[(-e- [u any] [v any]) undirected-edge?]{
 Create an undirected edge with endpoints @racket[u] and @racket[v].
                                                         
 @bold{NOT available inside verifier definitions}
}

@defproc[(-e-> [u any] [v any]) directed-edge?]{
 Create an directed edge from @racket[u] and @racket[v].
                              
 @bold{NOT available inside verifier definitions}
}

@defproc[(has-edge? [u any] [v any] [g graph?]) boolean?]{
 Check if there is an edge from @racket[u] to @racket[v] in graph
 @racket[g]. 
}

@defproc[(e-u [e edge]) any]{
  Get one endpoint of the edge @racket[e]. If @racket[e] is a directed edge, the result is
  the starting vertex.
}

@defproc[(e-v [e edge?]) any]{
  Get the other endpoint of the edge @racket[e], guaranteed to be different than the result of
  @racket[(e-u e)]. If @racket[e] is a directed edge, the result is the ending vertex.
}

@defproc[(incident? [e edge?] [v any]) boolean?]{
 Check if there is @racket[v] is an endpoint of edge @racket[e].
}

@defproc[(subgraph-of? [g1 graph?] [g2 graph?]) boolean?]{
 Check if @racket[g1] is a subgraph of @racket[g2].
}

@defproc[(neighbors [g graph?] [u any]) (setof any)]{
 Get the set of (out-)neighbors of vertex @racket[u] in graph @racket[g]. If @racket[g] is
 a directed graph, the result is the set of vertices that @racket[u] directs to.
}

@defproc[(in-neighbors [g graph?] [u any]) (setof any)]{
 Get the set of in-neighbors of vertex @racket[u] in graph @racket[g]. The result is the same
 as @racket[(neighbors g u)] when @racket[g] is undirected. If @racket[g] is
 a directed graph, the result is the set of vertices that direct to @racket[u].
}

@defproc[(create-graph [V (setof any)] [E (setof edge?)] [#:directed? directed boolean? #f]) graph?]{
 Create a graph with vertex set @racket[V] and edge set @racket[E]. @racket[directed] specifies
whether the graph is directed or not. 
}

@defproc[(create-graph-from-edges [E (setof edge?)] [#:directed? directed boolean? #f]) graph?]{
 Create a graph from the edge set @racket[E]. The vertex set of the resulting graph is the set of edgepoints
 of all edges in @racket[E]. @racket[directed] specifies whether the graph is directed or not. 
}

@defproc[(remove-edges [g graph?] [es (setof edge)]) graph?]{
 Produce a new graph by removing the set of edges @racket[es] from graph @racket[g].
 The vertices of the resulting graph will be the same as @racket[g].
}

@defproc[(remove-vertices [g graph?] [vs (setof any)]) graph?]{
 Produce a new graph by removing the set of vertices @racket[vs] from graph @racket[g].
 All edges with at least one endpoint in @racket[vs] are also removed in the resulting graph.
}

@defproc[(connected? [g graph?]) boolean?]{
  Test if graph @racket[g] is connected. When @racket[g] is directed, weak connectivity is tested 
}

@defproc[(acyclic? [g graph?]) boolean?]{
  Test if graph @racket[g] is acyclic. 
}

@defproc[(st-path? [g graph?] [s any] [t any]) boolean?]{
  Test if graph @racket[g] is an @racket[s]-@racket[t] path.
}