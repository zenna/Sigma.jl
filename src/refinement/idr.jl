function dls(f::Callable, Y_sub, depth::Int64,
             depth_limit::Int64, t::Tree, node::Node; box_budget = 300000)
  # Resolve SAT status is unknown
  if node.status == UNKNOWNSAT
    image = call(f,node.data)
    node.status = if subsumes(Y_sub, image) SAT
                  elseif overlap(image,Y_sub) MIXEDSAT
                  else UNSAT end
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
function pre_deepening{T, F <: Callable}(f::F, Y_sub, X::T; box_budget = 300000, max_depth = 4)
  tree = Tree(Node(rand(Uint64), UNKNOWNSAT, X))
  for depth_limit = 1:max_depth
    println("Deepening Depth Limit", depth_limit)
    tree = dls(f, Y_sub, 0, depth_limit, tree, root(tree), box_budget = box_budget)
  end
  println(length(tree.nodes))
  tree
end
