## Metropolis Hastings querying

## TODO:
## Be able to subdivide parameterised on which dimensions, split_point et


function add_children!(f::Callable, Y, t::WeightedTree, node::Node)
  children = middle_split(node.data)
  weight = 1/length(children)
  for i = 1:length(children)
    childnode = Node(0,checksat(f,Y,children[i]),children[i])
    add_child!(t, childnode, node.id, weight)
  end
  node
end

# Add weighted children
function add_children!(f::Callable, Y, t::WeightedTree, node::Node, depth::Int, split::Function)
  children::Vector{(Domain,Float64)} = split(node.data, depth)
  childnodes = Node[]
  weights = Float64[]

  for i = 1:length(children)
    #FIXME USELESS 0 index NODE is CODEMSELL
    satstatus = checksat(f,Y,children[i][1])
    if satstatus != UNSAT
      childnode = Node(0,satstatus,children[i][1])
      push!(childnodes, childnode)
      push!(weights, children[i][2])
    end
  end

  # rescale the weights to account for fact that UNSAT are removed
  pnormalize!(weights)

  @assert length(weights) == length(childnodes)
  @assert length(childnodes) > 0
  # add children
  for i = 1:length(childnodes)
    add_child!(t, childnodes[i], node.id, weights[i])
  end

  return node
end

# How should we split an abstract element X found at depth d in refinement
# Sets set of domains and weight with which to choose them
# function split_dim_by_depth(X::Domain, depth::Int64j) end

function weighted_middle_split(o::Omega, depth::Int)
  splitted = middle_split(o::Omega)
  transitionprob = 1/length(splitted)
  [(event, transitionprob) for event in splitted]
end

# function split_along_dims(o::Omega, dims::Dict{Int, Float64})
#   ks = collect(keys(o.intervals))
#   vs = collect(values(o.intervals))
# end


# function middle_split(o::Omega, d::depth)
#   ks = collect(keys(o.intervals))
#   vs = collect(values(o.intervals))
#   box = convert(Box,vs)
#   z = middle_split(box)
#   map(x->Omega(Dict(ks,convert(Vector{Interval},x))),z)
# end

# Like greedy! but better named and smarter
function proposebox!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree, split::Function = weighted_middle_split)
  node::Node{D} = root(t)
  depth = 0
  logq = 0.0 # == log(1.0)

  @label start
  if node.status == SAT
    return node.data, logq
  elseif node.status == PARTIALSAT
    # Add children if none there
    if !has_children(t,node) add_children!(f, Y, t, node, depth, split) end

    children = getchildren(t,node)
    # FIXME: HANDLE Case all children are unsat!
    transitionprobs = Float64[child[2] for child in children]
    @assert isapprox(sum(transitionprobs),1.0)

    # sample a PARTIALSAT / SAT child
    # PERF: Instead of recreating this categorical, each iteration, store it!
    childid, q = children[rand(Categorical(transitionprobs))]
    child = node_from_id(t, childid)

    # Go a level deeper in tree
    depth += 1
    logq += log(q)
    if depth > 1
      @show length(children)
      @show depth, child.status
      @show child.data
    end

    if child.status == SAT
      return child.data, logq
    elseif child.status == PARTIALSAT
      node = child
      @goto start
    elseif child.status == UNSAT
      @unexpected
    end
  else
    @unexpected
  end
end


# function greedy!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree)
#   node = root(t)
#   depth = 0

#   @label start
#   if node.status == SAT
# #     @show "We're SAT"
#     return node, depth
#   elseif node.status == PARTIALSAT
#     # Add children if none there
#     if !has_children(t,node) add_children!(f, Y, t, node) end

#     # Randomly select a child
#     child = node_from_id(t,rand_select(children_ids(t, node))[1])
#     if child.status == SAT
#       depth += 1
#       return child.data, depth
#     elseif child.status == PARTIALSAT
#       node = child
#       depth += 1
# #       @show "MIXED going back to start $depth"
#       @goto start
#     elseif child.status == UNSAT
#       # DO UPDATES
#       depth = 0
# #       @show "UNSAT going back to start $depth"
#       node = root(t)
#       @goto start
#     end
#   elseif node.status == UNSAT
#     return error("UNSAT")
#   end
# end

# Preimage of Y under F, unioned with X
function pre_mh{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5, max_iters = 1E5, stepspersample = 1)
  # Construct tree with root node as preimage
  t = WeightedTree(Node(1, checksat(f,Y,X), X))
  boxes = D[]

  # We use log for numercal stability
  box, logq = proposebox!(f,Y,X,t)
  logp = log(measure(box))

  naccepted = 0
  nsteps = 0
  while nsteps < max_iters
    nextbox, nextlogq = proposebox!(f,Y,X,t)
    nextlogp = log(measure(nextbox))

    loga = nextlogp + logq - logp - nextlogq
    a = exp(loga)

    # MH accept/reject step
    if a >= 1 || rand() < a
      naccepted += 1
      box = nextbox
      logp = nextlogp
      logq = nextlogq
    end

    # Statistics
    if nsteps % 50 == 1
      println("acceptance ratio: $(naccepted/nsteps)")
      println("tree vertices: $(length(t.nodes))")
    end

    # Store current state every stepspersample-th timestep
    if nsteps % stepspersample == 0
      push!(boxes,box)
    end
    nsteps += 1
  end
  boxes
end

# # Preimage of Y under F, unioned with X
# function pre_mh{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5, max_iters = 1E5, stepspersample = 1)
#   # Construct tree with root node as preimage
#   t = WeightedTree(Node(1, checksat(f,Y,X), X))
#   boxes = D[]

#   currbox, currp = greedy!(f,Y,X,t)
#   currmeasure = measure(currbox)

#   nsteps = 0
#   while nsteps < max_iters
#     nextbox, nextp = greedy!(f,Y,X,t)
#     nextmeasure = measure(nextbox)
#     a1 = nextmeasure / currmeasure
#     # FIXME: ndims is a bit hacky, will surely break in places
#     a2 = 2^(float(ndims(nextbox) * (nextp - currp)))
# #     a2 = currp / nextp
#     a = a1 * a2

# # #     if nsteps % 50 == 0
# #     @show a1,a2,a
# #     @show currp, nextp
# # #     end

#     # MH accept/reject step
#     if a >= 1 || rand() < a
#       currbox = nextbox
#       currmeasure = nextmeasure
#       currp = nextp
#     end

#     # Store current state
#     if nsteps % stepspersample == 0
#       push!(boxes,currbox)
#     end
#     nsteps += 1
#   end
#   boxes
# end
