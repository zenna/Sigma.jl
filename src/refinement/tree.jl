type Node{T}
  id::Int
  status::SatStatus
  data::T
end

abstract Tree
type UnweightedTree <: Tree
  id_counter::Int
  nodes::Vector{Node}
  children::Vector{Vector{Int}}
  UnweightedTree(n::Node,c::Vector{Vector{Uint64}}) = new(n.id+1,n,c)
  UnweightedTree() = new(1,[],[])
end

UnweightedTree(n::Node) = UnweightedTree(n.id+1,n,[])
root(t::UnweightedTree) = t.nodes[1]

function add_child!(t::UnweightedTree, n::Node, parent_id::Int)
  add_node!(t,n)
  push!(t.children[parent_id],n.id)
  n
end

## Weighted Tree
## ============

typealias NodeWeight (Int, Float64)
getnodeid(nw::NodeWeight) = nw[1]
getweight(nw::NodeWeight) = nw[2]

type WeightedTree <: Tree
  id_counter::Int
  nodes::Vector{Node}
  children::Vector{Vector{NodeWeight}}
end

WeightedTree() = WeightedTree(1,[],Vector[[]])
WeightedTree(n::Node,c::Vector{Vector{NodeWeight}}) = WeightedTree(n.id+1,n,c)
WeightedTree(n::Node) = WeightedTree(n.id+1,[n],Vector[[]])
root(t::WeightedTree) = t.nodes[1]

function add_child!(t::WeightedTree, n::Node, parent_id::Int, weight::Float64)
  add_node!(t,n)
  push!(t.children[parent_id],(n.id,weight))
  n
end

function update_edgeweight!(t::WeightedTree, parent::Node, child::Node,
                            weight::Float64)
  for i = 1:length(t.children[parent.id])
    if t.children[parent.id][i][1] == child.id
      t.children[parent.id][i][2] = weight
      break
    end
  end
end

## General Tree
## ============

function add_node!(t::Tree, n::Node)
  n.id = t.id_counter
  t.id_counter += 1
  push!(t.nodes,n)
  push!(t.children,[])
  n
end

function remove_edge!(t::WeightedTree, parent::Node, child::Node)
  for i = 1:length(t.children[parent.id])
    if t.children[parent.id][i][1].id == child.id
      deleteat!(t.children[parent.id],i)
      break
    end
  end
end

has_children(t::Tree, n::Node) = !isempty(t.children[n.id])
node_from_id(t::Tree, node_id::Int) = t.nodes[node_id]
children_ids(t::Tree, n::Node) = t.children[n.id]
getchildren(t::Tree, n::Node) = t.children[n.id]
getchild(t::Tree, n::Node, i::Int) = t.children[n.id][i]

# All weights of a child should sum to 1
function normalize_children!(t::Tree, n::Node)
  weights = Float64[]
  for (child,weight) in getchildren(t, n)
    push!(weights, weight)
  end

  pnormalize!(weights)
  for i = 1:length(weights)
    t.children[n.id][i] = (t.children[n.id][i][1], weights[i])
  end
end

## SAT STUFF
## =========

function sat_tree_data(t::Tree)
  a::Vector{Omega} = map(n->n.data,filter(n->n.status==SAT,t.nodes))
  a #For some reason this line can't be removed if i want to enforce types
end

function mixedsat_tree_data(t::Tree)
  a::Vector{Omega} = map(n->n.data,filter(n->(n.status != UNSAT)
                                              && (!has_children(t,n)),t.nodes))
  a
end
