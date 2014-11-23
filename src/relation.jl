import Base.isequal
import Base.union

## TODO
## ====
# Avoid recreating new vertices when not necessary
# Implement conversion to dReal
# Implement FreeVariables and Compositional Relations

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
abstract Vertex{T}
# Positioned Vertex
typealias PosVertex (Vertex, Int)

immutable Relation
  vertices::Set{Vertex}
  inedges::Dict{Vertex,Vector{PosVertex}}
  outedges::Dict{Vertex,Vector{PosVertex}}
end

Relation() = Relation(Set{Vertex}(), Dict{Vertex,Vector{PosVertex}}(),
                      Dict{Vertex,Vector{PosVertex}}())

add_vertex!(r::Relation, v::Vertex) = push!(r.vertices,v)

# add an edge from v1 to v2
function add_edge!(r::Relation, posv1::PosVertex, posv2::PosVertex)
  v1, pos1 = posv1
  v2, pos2 = posv2
  add_vertex!(r,v1)
  add_vertex!(r,v2)
  checkpush!(r.outedges, v1, [posv2])
  checkpush!(r.inedges, v2, [posv1])
end

# Add a vector value to a dict if key doesn't exist, if it does, append elements
function checkpush!{P<:PosVertex}(d::Dict{Vertex,Vector{PosVertex}}, key::Vertex, value::Vector{P})
  if haskey(d,key) push!(d[key],value...)
  else d[key] = value end
end

# Merge all vertices and edges of relation
function union(x::Relation, y::Relation)
  # Add all new vertices
  vs = union(x.vertices,y.vertices)
  inedges = Dict{Vertex,Vector{PosVertex}}()
  outedges = Dict{Vertex,Vector{PosVertex}}()

  # Add edges
  for v in vs, xy in (x,y)
    # Check for all vertices whether they exist in x or y, if so, add
    if haskey(xy.inedges,v) checkpush!(inedges, v, xy.inedges[v]) end
    if haskey(xy.outedges,v) checkpush!(outedges, v, xy.outedges[v]) end
  end
  Relation(vs,inedges,outedges)
end

## Vertices
## ========
typealias VertexIdType Int

immutable PrimitiveVertex{T} <: Vertex{T}
  s::Symbol
end
isequal(x::PrimitiveVertex, y::PrimitiveVertex) = x.s == y.s

const plus_rel = PrimitiveVertex{(Real,Real,Real)}(:+)
const minus_rel = PrimitiveVertex{(Real,Real,Real)}(:-)
const mul_rel = PrimitiveVertex{(Real,Real,Real)}(:*)
const div_rel = PrimitiveVertex{(Real,Real,Real)}(:/)
const gt_rel = PrimitiveVertex{(Real,Real)}(:>)
const gte_rel = PrimitiveVertex{(Real,Real)}(:>=)
const lt_rel = PrimitiveVertex{(Real,Real)}(:<)
const lte_rel = PrimitiveVertex{(Real,Real)}(:<=)

rangetype(v::Vertex) = typeof(v).parameters[1]
arity(v::PrimitiveVertex) = length(rangetype(v))

# Anonymous variable
type AnonVertex{T} <: Vertex{T}
  index::Int
  relation::Relation
end

AnonVertex(T::DataType, r::Relation) = AnonVertex{T}(genint(),r)

# Concrete values
immutable ValueVertex{T} <: Vertex{T}
  index::Int
  x::T
end

# Value vertices are defined only by their value (x)
isequal(x::ValueVertex, y::ValueVertex) = x.x == y.x
ValueVertex{T}(x::T) = ValueVertex{T}(genint(),x)

# VarVertexs point to named components of relations
type VarVertex{T} <: Vertex{T}
  index::VertexIdType
  relation::Relation
  function VarVertex(index::VertexIdType)
    r = Relation()
    v = new(index)
    add_vertex!(r,v)
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

# Two Var vertices are the same when their ids are identical, since all ids are unique
# FIXME: This may cause problems if you redefine variables
isequal(x::VarVertex, y::VarVertex) = x.index == y.index

## Graph stuff
## ===========
# Create an empty generic graph of type vertex type V

function relate!{V <: Vertex}(r::Relation, vp::PrimitiveVertex, args::Vector{V})
  @assert arity(vp) == length(args)
  # types of variables and primitive relation must match
  [@assert rangetype(args[i]) == rangetype(vp)[i] for i = 1:length(args)]

  # Add the verties
  push!(r.vertices, vp)
  union!(r.vertices, args)
  for i = 1:length(args)
    add_edge!(r,(args[i],1),(vp,i))
  end
  r
end

# parsearg(v::ValueVertex) = v.x
# parsearg(v::VarVertex) = v.index
# parsearg(v::AnonVarVertex) = convert(::

# function ithchild(rel, i::Int)

# function convert(::Type{Vector{Expr}}, r::RelationGraph)
#   # rels is a list of all the PrimitiveRelVars
#   rels = primitiverelations(r)

#   exprs = Expr[]
#   while !isempty(rels)
#     rel = pop!(rels)
# #     args = [parsearg(ithchild(rel,i)) for i = 1:arity(rel)]
#     args = Vector(Any,arity(rel))
#     expr = :(rel $(args...))
#     if isbool_valued(rel)
#       put expr on AnonymousVariable
#     else
#       push!(exprs, expr)
#     end
#   end
#   exprs
# end

## Primitive Relation Operations
## =============================

promote_type(Bool,Bool)

# Ternary Relations
for op = (:+, :-, :/,:*,)
  @eval begin
    function ($op){T1 <: Number,T2 <: Number}(x::Vertex{T1}, y::Vertex{T2})
      r = union(x.relation,y.relation) # new relation

      # operator vertex
      opsymb = symbol(string($op))
      RETURNT = promote_type(T1, T2)
      opv = PrimitiveVertex{(T1, T2, RETURNT)}(opsymb)

      # update relation that x,y,x point to
      x.relation = r
      y.relation = r
      z = AnonVertex(RETURNT,r) # output variable

      # add necessary elements to graph
      relate!(r,opv,[x,y,z])
      return z
    end
  end
end

union_relation{T}(x::ValueVertex{T}, y::ValueVertex{T}) = error("ValueVertex has no rel")
update_relation!(v::Vertex,r::Relation) = (v.relation = r; return v)
update_relation!(v::ValueVertex,r::Relation) = v
union_relation(x::Vertex,y::Vertex) = union(x.relation,y.relation)
union_relation(x::Vertex, y::ValueVertex) = x.relation
union_relation(x::ValueVertex, y::Vertex) = y.relation

for op = (:>, :>=, :<,:<=,)
  @eval begin
    function ($op){T1 <: Number,T2 <: Number}(x::Vertex{T1}, y::Vertex{T2})
      r = union_relation(x,y) # new relation

      # operator vertex
      opsymb = symbol(string($op))
      opv = PrimitiveVertex{(T1, T2)}(opsymb)

      # update relation that x,y,x point to
      update_relation!(x,r)
      update_relation!(y,r)

      # add necessary elements to graph
      relate!(r,opv,[x,y])
      r
    end

    # Relation with concrete values create ValueVertexs
    function ($op){T1 <: Number,T2 <: Number}(x::Vertex{T1}, y::T2)
      ($op)(x,ValueVertex(y))
    end
    function ($op){T1 <: Number,T2 <: Number}(x::T1, y::Vertex{T2})
      ($op)(ValueVertex(x),y)
    end
  end
end
