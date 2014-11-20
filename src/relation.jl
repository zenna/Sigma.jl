using Graphs
import Graphs.make_vertex
import Graphs.add_vertex!

typealias VertexIdType Int

## Relation
## ========

# A relation is  represented by a bipartite graph with edges between named variables,
# anonymous variables, values and primitive or compound relations
# Primitive relations correspond to primitive functions < > / * + - +
# Variables correspond to components of such relations.
# Hence there are two types of variables:
# - Variables which correspond to relations themselves, often called RelVars.
# - Variables which correspond to components - Vars

# A relation is represented by its constraint graph
# A constraint graph is hyper graph,
# We represent this as a bipartite graph between
# variables and primitive or compund relations
immutable Relation
  vertices = Set{Vertex}
  edges::Dict{Vertex,(Vertex, Int)}
end

add_vertex!(r::Relation, v::Vertex) = push!(r.vertices,v)
function add_edge!(r::Relation, v1::Vertex, v2::Vertex)
  add_vertex!(r,v1)
  add_vertex!(r,v2)
  r.edges[v1]
end

function relate!(r::Relation, vp::PrimitiveVertex, )
  @assert arity(vp) == length(args)
  union!(r.vertices)
  for i = 1:length(args)
    add_edge!(r,args[i],(vp,i))
  end
  r
end

Relation() = Relation(empty_graph(Vertex))

## Vertices
## ========
abstract Vertex{T}

immutable PrimitiveVertex{T} <: Vertex{T}
  s::Symbol
end

# Anonymous variable
immutable AnonVertex{T} <: Vertex{T}
  index::Int
end

# Concrete values
immutable ValueVertex{T} <: Vertex{T}
  index::T
  x::T
end

# VarVertexs point to named components of relations
type VarVertex{T} <: Vertex{T}
  index::VertexIdType
  relation::Relation
  function VarVertex(index::VertexIdType)
    r = Relation()
    v = new(index)
    add_vertex!(r.graph,v)
    v.relation = r
    v
  end
  VarVertex(index::VertexIdType, relation::Relation) =
    new(index,relation)
end

VarVertex(T::DataType, index::VertexIdType) = VarVertex{T}(index)
VarVertex(T::DataType) = VarVertex(T,genint())
VarVertex(T::DataType, r::Relation) = VarVertex{T}(genint(),r)
Var = VarVertex

## Graph stuff
## ===========
# Create an empty generic graph of type vertex type V

parsearg(v::ValueVertex) = v.x
parsearg(v::VarVertex) = v.index
parsearg(v::AnonVarVertex) = convert(::

# function ithchild(rel, i::Int)

function convert(::Type{Vector{Expr}}, r::RelationGraph)
  # rels is a list of all the PrimitiveRelVars
  rels = primitiverelations(r)

  exprs = Expr[]
  while !isempty(rels)
    rel = pop!(rels)
    # if rel is a characteristic function and its output is anonymos, go up one
    args = [parsearg(ithchild(rel,i)) for i = 1:arity(rel)]
    args = Vector(Any,arity(rel))
    expr = :(rel $(args...))
  push!(exprs, expr)
end

function empty_graph(V::DataType)
  return graph(V[], Edge{V}[]; is_directed=false)
end

make_vertex{T}(g::GenericGraph, v::VarVertex{T}) = VarVertex{T}(num_vertices(g) + 1)

function add_vertex!{V <: Vertex}(g::GenericGraph{Vertex}, v::V)
  @show "todo: check doesn't already exis"
  push!(g.vertices, v)
  push!(g.finclist, Int[])
  push!(g.binclist, Int[])
  v
end

function add_edge!{V1<:Vertex, V2<:Vertex}(g::GenericGraph, u::V1, v::V2, e)
  # add an edge e between u and v
  ui = vertex_index(u, g)::Int
  vi = vertex_index(v, g)::Int

  push!(g.edges, e)
  push!(g.finclist[ui], e)
  push!(g.binclist[vi], e)

  if !g.is_directed
    rev_e = revedge(e)
    push!(g.finclist[vi], rev_e)
    push!(g.binclist[ui], rev_e)
  end
  e
end

# add_edge!{V1<:Vertex, V2<:Vertex}(g::GenericGraph, u::V1, v::V2 = add_edge!(g, u, v, make_edge(g, u, v)))

# VertexIdType
# Var(T::DataType, x) = Var{T}()
# Var(T::DataType, s::Symbol) = Var{T}(KeyVertex{Symbol}(genint(),s))

merge_relations(x::Relation, y::Relation) = Relation(merge_graphs(x.graph,y.graph))

# merge two graphs together
function merge_graphs{G}(x::GenericGraph{G}, y::GenericGraph{G})
  g = empty_graph(G)

  # Add edges
  for v in union(vertices(x), vertices(y))
    add_vertex!(g,v)
  end

  # Add edges
  for edge in union(edges(x), edges(y))
    add_edges!(g,edge)
  end
  g
end

## Primitive Relation Operations
## =============================

# Ternary Relations
for (op,T1,T2,RETURNT) =
    ((:+,Real,Real,Real),
     (:-,Real,Real,Real),
     (:/,Real,Real,Real),
     (:*,Real,Real,Real))
  #   b = symbol($op)
  @eval begin
    function ($op)(x::VarVertex{$T1}, y::VarVertex{$T2})
      let op = $op, T1 = $T1, T2 = $T2, RETURNT = $RETURNT
        r = merge_relations(x.relation,y.relation) # new relation

        # operator vertex
        opsymb = symbol(string($op))
        opv = PrimitiveVertex{($T1, $T2, $RETURNT)}(opsymb)

        # update relation that x,y,x point to
        x.relation = r
        y.relation = r
        z = VarVertex($T1,r) # output variable

        # add necessary elements to graph
        @show typeof(r.graph), z
        add_vertex!(r.graph, z)
        add_vertex!(r.graph, opv)

        # Add hyper edges
        add_edge!(r.graph,x,opv)
        add_edge!(r.graph,y,opv)
        add_edge!(r.graph,z,opv)

        return z
      end
    end
  end
end

## Example
## =======
# V = VarVertex(Real)
# X = Var(Real)
# Y = Var(Real)
# X + Y
# typeof(X.relation.graph)
## Overall outline
## ==============
#
# X.relation
# vertice

# v = VarVertex{Real}(3)
# add_vertex!(g,v)
# Z = Var(Real)
# Y = Var(Real)
# X + Y > Z
