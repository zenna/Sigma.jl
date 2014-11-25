## Metropolis Hastings querying

function add_children!(f::Callable, Y, t::WeightedTree, node::Node)
  children = middle_split(node.data)
  weight = 1/length(children)
  for i = 1:length(children)
    childnode = Node(0,checksat(f,Y,children[i]),children[i])
    add_child!(t, childnode, node.id, weight)
  end
  node
end

function greedy!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree)
  node = root(t)
  depth = 0

  @label start
  if node.status == SAT
#     @show "We're SAT"
    return node, depth
  elseif node.status == MIXEDSAT
    # Add children if none there
    if !has_children(t,node) add_children!(f, Y, t, node) end

    # Randomly select a child
    child = node_from_id(t,rand_select(children_ids(t, node))[1])
    if child.status == SAT
      depth += 1
      return child.data, depth
    elseif child.status == MIXEDSAT
      node = child
      depth += 1
#       @show "MIXED going back to start $depth"
      @goto start
    elseif child.status == UNSAT
      # DO UPDATES
      depth = 0
#       @show "UNSAT going back to start $depth"
      node = root(t)
      @goto start
    end
  elseif node.status == UNSAT
    return error("UNSAT")
  end
end

# Preimage of Y under F, unioned with X
function pre_mh{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5, max_iters = 1E5, stepspersample = 1)
  # Construct tree with root node as preimage
  t = WeightedTree(Node(1, checksat(f,Y,X), X))
  boxes = D[]

  currbox, currp = greedy!(f,Y,X,t)
  currmeasure = measure(currbox)

  nsteps = 0
  while nsteps < max_iters
    nextbox, nextp = greedy!(f,Y,X,t)
    nextmeasure = measure(nextbox)
    a1 = nextmeasure / currmeasure
    # FIXME: ndims is a bit hacky, will surely break in places
    a2 = 2^(float(ndims(nextbox) * (nextp - currp)))
#     a2 = currp / nextp
    a = a1 * a2

# #     if nsteps % 50 == 0
#     @show a1,a2,a
#     @show currp, nextp
# #     end

    # MH accept/reject step
    if a1 >= 1 || rand() < a
      currbox = nextbox
      currmeasure = nextmeasure
      currp = nextp
    end

    # Store current state
    if nsteps % stepspersample == 0
      push!(boxes,currbox)
    end
    nsteps += 1
  end
  boxes
end
