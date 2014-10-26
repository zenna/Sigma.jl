# Pre-image Computation:
# Given a function f:X->Y and Y' ⊆ Y -
# -- find X' ⊆ X such that f(x') ∈ Y'
## ===================================
## Iterative Deepening Preconditioning

immutable SatStatus
  status::Uint8
end

const UNSAT = SatStatus(0x0)
const SAT = SatStatus(0x1)
const MIXEDSAT = SatStatus(0x2)
const UNKNOWNSAT = SatStatus(0x3)

type Node{T}
  id::Uint64
  status::SatStatus
  data::T
end

type Tree
  id_counter::Uint64
  nodes::Vector{Node}
  children::Vector{Vector{Uint64}}
  Tree(n::Node,c::Vector{Vector{Uint64}}) = new(1,n,c)
  Tree(n,c) = new(1,n,c)
end

Tree(n::Node) = (t = Tree([],[]); add_node!(t,n); t)
root(t::Tree) = t.nodes[1]

function add_node!(t::Tree, n::Node)
  n.id = t.id_counter
  t.id_counter += 1
  push!(t.nodes,n)
  push!(t.children,[])
  n
end

function add_child!(t::Tree, n::Node, parent_id::Uint64)
  add_node!(t,n)
  push!(t.children[parent_id],n.id)
  n
end

has_children(t::Tree, n::Node) = !isempty(t.children[n.id])
node_from_id(t::Tree, node_id::Integer) = t.nodes[node_id]
children_ids(t::Tree, n::Node) = t.children[n.id]

function sat_tree_data(t::Tree)
  a::Vector{Omega} = map(n->n.data,filter(n->n.status==SAT,t.nodes))
  a #For some reason this line can't be removed if i want to enforce types
end

function mixedsat_tree_data(t::Tree)
  a::Vector{Omega} = map(n->n.data,filter(n->(n.status != UNSAT)
                                              && (!has_children(t,n)),t.nodes))
  a
end

function dls(f::Union(RandVar, Function), Y_sub, depth::Integer, depth_limit::Integer, t::Tree, node::Node; box_budget = 300000)
  # Resolve SAT status is unknown
  if node.status == UNKNOWNSAT
#     image = f(node.data)
    image = call(f,node.data)
    satstatus = if subsumes(Y_sub, image) SAT elseif overlap(image,Y_sub) MIXEDSAT else UNSAT end
    node.status = satstatus
  end

  if length(t.nodes) >= box_budget
    return t
  end

  if node.status == MIXEDSAT
    if has_children(t, node)
      for child_id in children_ids(t, node)
        child = node_from_id(t,child_id)
        if child.status == MIXEDSAT && depth + 1 < depth_limit
           t = dls(f, Y_sub, depth + 1, depth_limit, t, child; box_budget = box_budget)
        end
      end
    elseif depth + 1 < depth_limit
      children_data =   middle_split(node.data)
      children_nodes = Array(typeof(node),length(children_data)) # DO THIS LAZILY
#       children_nodes = Array(Node{Omega{EnvVar{Set{Symbol},Interval}}},length(children_data)) # DO THIS LAZILY
      for i = 1:length(children_data)
        new_node = Node(rand(Uint64), UNKNOWNSAT, children_data[i])
        children_nodes[i] = new_node
        new_child = add_child!(t, children_nodes[i], node.id)
        t = dls(f, Y_sub, depth + 1, depth_limit, t, new_child; box_budget = box_budget)

        # Poor budget hack
        if length(t.nodes) >= box_budget
          return t
        end
      end
    end
  elseif node.status == UNSAT || node.status == SAT
    t
  end
  t
end

# Preimage refinement based on iterative deepening
# Returns under and overapproximating sets of boxes
function pre_deepening{T}(f::Union(RandVar, Function), Y_sub, X::T; box_budget = 300000, max_depth = 4)
  tree = Tree(Node(rand(Uint64), UNKNOWNSAT, X))
  for depth_limit = 1:max_depth
    println("Deepening Depth Limit", depth_limit)
    tree = dls(f, Y_sub, zero(Uint), depth_limit, tree, root(tree), box_budget = box_budget)
  end
  println(length(tree.nodes))
  tree
end

# ## This only looks at the leaf nodes
# function dlsleaf(f::Function, Y_sub, depth::Integer, depth_limit::Integer, t::Tree, node::Node
#                  leaflist::Vector{Node}; box_budget)
#   image = f(node.data)
#   satstatus = if subsumes(Y_sub, image) SAT elseif overlap(image,Y_sub) MIXEDSAT else UNSAT end
#   node.status = satstatus

#   if length(t.nodes) >= box_budget
#     return t, leaflist
#   end

#   if node.status == MIXEDSAT && depth + 1 < depth_limit
#     children_data =   middle_split(node.data)
#     children_nodes = Array(typeof(node),length(children_data)) # DO THIS LAZILY
#     for i = 1:length(children_data)
#       new_node = Node(rand(Uint64), UNKNOWNSAT, children_data[i])
#       children_nodes[i] = new_node
#       new_child = add_child!(t, children_nodes[i], node.id)
#       push!(leaflist,new_child)
#     end
#   end
#     t, leaflist
# end

# function pre_deepend{T}(f::Function, Y_sub, X::T, box_budget, max_depth)
#   tree = Tree(Node(rand(Uint64), UNKNOWNSAT, X))
#   leaflist::Vector
#   for depth_limit = 1:max_depth
#     println("Deepening Depth Limit", depth_limit)
#     tree = dls(f, Y_sub, zero(Uint), depth_limit, tree, root(tree), box_budget = box_budget)
#   end
#   println(length(tree.nodes))
#   tree
# end


## ===========================================
## Greedy Preconditioning - Single Covering Box

function pre_greedy(f::Function, y, bs, depth = 1)
  @label start_again
  println("starting again,", length(bs), sum(map(volume,bs)))
  i = 1
  for b in bs
    image = f(to_intervals(b))
    println(i, image)
    i += 1
    if subsumes(y,image)
      return b
    elseif overlap(image,y)
      bs = middle_split(b)
      println("Going back")
      @goto start_again
    end
  end
  println("Got to the end somehow")
end
