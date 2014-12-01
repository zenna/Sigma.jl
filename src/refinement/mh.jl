## Metropolis Hastings querying

## TODO:
## Be able to subdivide parameterised on which dimensions, split_point et

function fraction_sat(Y::RandVar{Bool}, o::Omega, n::Int)
  samples = [rand(o) for i = 1:n]
  for sample in samples
    if call(Y,sample)
      @show sample
      error("stop right there")
    end
  end
  count(identity, [call(Y,rand(o)) for i = 1:n])/n
end

## Splitting Strategies
## ====================

# This splits along all dimensions, ignores the depth
function weighted_mid_split(o::Omega, depth::Int)
  splitted = mid_split(o::Omega)
  transitionprob = 1/length(splitted)
  [(event, transitionprob) for event in splitted]
end

# This splits along the 1st dimension in for the first split
# The second dimension for the second split, then cycles
function weighted_partial_split(o::Omega, depth::Int)
  dimindices = collect(keys(o.intervals))
  ndims = length(dimindices)

  if (depth % length(dimindices)) + 1 > length(dimindices)
    @show depth
    @show dimindices
  end

  dimtosplit = dimindices[(depth % length(dimindices)) + 1]
  splitted = mid_partial_split(o::Omega, [dimtosplit])
  transitionprob = 1/length(splitted)
  [(event, transitionprob) for event in splitted]
end

# Randomly select a dimension
function rand_partial_split(o::Omega, depth::Int)
  dimindices = collect(keys(o.intervals))
  splitted = mid_partial_split(o::Omega, [rand_select(dimindices)])
  transitionprob = 1/length(splitted)
  [(event, transitionprob) for event in splitted]
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
#   @assert length(childnodes) > 0
  if length(childnodes) == 0 # No children (due to imprecision)
    return []
  else
    # add children
    for i = 1:length(childnodes)
      add_child!(t, childnodes[i], node.id, weights[i])
    end
    return getchildren(t,node)
  end
end

## Single-path refinement
## =====================

# Like greedy! but better named and smarter
function proposebox!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree,
                                  split::Function = weighted_partial_split)
  node::Node{D} = root(t)
  depth = 0
  niterations = 0
  logq = 0.0 # == log(1.0)


  @label start
  niterations += 1

  if niterations % 100 == 0
    if niterations > 40000
      error("Too many iterations")
    end
    @show length(t.nodes)
    @show niterations
    if length(t.nodes) > 100000
      error("Tree is too big - will run out of memory")
    end
  end

  if node.status == SAT
#     @show "stopped at initial sat"
    return node.data, logq
  elseif node.status == PARTIALSAT
    # Add children if none there
    children = if !has_children(t,node) add_children!(f, Y, t, node, depth, split)
              else getchildren(t,node) end

    # Start again
    if isempty(children)
      @show "children empty, starting again at root"
      node = root(t)
      @goto start
    end

#     children = getchildren(t,node)
    # FIXME: HANDLE Case all children are unsat!
    transitionprobs = Float64[child[2] for child in children]
    @assert isapprox(sum(transitionprobs),1.0)

    # sample a PARTIALSAT / SAT child
    # PERF: Instead of recreating this categorical, each iteration, store it!
    cindex = rand(Categorical(transitionprobs))
    childid, q = children[cindex]
    child = node_from_id(t, childid)
#     @show length(children)
#     @show child
#     @show cindex
#     @show child.data
#     @show measure(child.data)
#     @show niterations, depth

    af = fraction_sat(f,child.data,100)
    if niterations % 100 == 0 || af > 0
      @show af, depth
    end
    if af > 0 error("We got a point after $niterations niterations") end

    # Go a level deeper in tree
    depth += 1
    logq += log(q)
#     if depth > 0
#       @show length(children)
#       @show depth, child.status
#       @show child.data
#     end

    if child.status == SAT
#       @show "Found SAT child"
      return child.data, logq
    elseif child.status == PARTIALSAT
      node = child
#       @show "Found PARTIALSAT"
      @goto start
    elseif child.status == UNSAT
      @unexpected
    end
  else
    @unexpected
  end
end

# Preimage of Y under F, unioned with X
function pre_mh{D <: Domain} (f::Callable, Y, X::D; max_iters = 100, stepspersample = 1)
  # Construct tree with root node as preimage
  t = WeightedTree(Node(1, checksat(f,Y,X), X))
  boxes = D[]

  # We use log for numercal stability
  box, logq = proposebox!(f,Y,X,t)
  logp = logmeasure(box)
  println("Initial satisfying point found!, starting MH chain\n")


  naccepted = 0
  nsteps = 0
  while nsteps < max_iters
    nextbox, nextlogq = proposebox!(f,Y,X,t)
    nextlogp = logmeasure(nextbox)

    loga = nextlogp + logq - logp - nextlogq
    a = exp(loga)

#     @show exp(logp)
#     if true
#       @show a, loga
#       @show  box
#       @show logp, exp(logp), logq, exp(logq)
#       @show nextbox
#       @show  nextlogp, exp(nextlogp), nextlogq, exp(nextlogq)
#       println("tree vertices: $(length(t.nodes))")
#       println("")
#     end

    # MH accept/reject step
    if a >= 1 || rand() < a
      naccepted += 1
      box = nextbox
      logp = nextlogp
      logq = nextlogq
    end

    println("naccepted = $naccepted, nsteps = $(nsteps +1) ratio: $(naccepted/(nsteps+1))")

    # Statistics
#     if nsteps % 50 == 1

    # Store current state every stepspersample-th timestep
    if nsteps % stepspersample == 0
      push!(boxes,box)
    end
    nsteps += 1
  end
  boxes
end
