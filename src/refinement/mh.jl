## Metropolis Hastings querying
## ============================

function fraction_sat(Y::RandVar{Bool}, o::Omega, n::Int)
  samples = [rand(o) for i = 1:n]
#   for sample in samples
#     if call(Y,sample)
#       error("stop right there")
#     end
#   end
  count(identity, [call(Y,rand(o)) for i = 1:n])/n
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
                                  split::Function = rand_partial_split)
  niterations = 0
  @label restart # If we reach a spurrious unsat child, jump back here
  node::Node{D} = root(t)
  depth = 0
  logq = 0.0 # == log(1.0)

  @label start
  niterations += 1

  window(:pre_refine, niterations, t)

  if node.status == SAT # Condition is certain
    @show "stopped at initial sat"
    return node.data, logq
  elseif node.status == PARTIALSAT # Condition is certain
    # Add children if none there
    children = if !has_children(t,node) add_children!(f, Y, t, node, depth, split)
               else getchildren(t,node) end

    # Start again if a node has no children
    if isempty(children)
      @show "children empty, starting again at root"
      node = root(t)
      @goto restart
    end

    # FIXME: HANDLE Case all children are unsat!
    transitionprobs = Float64[child[2] for child in children]
    @assert isapprox(sum(transitionprobs),1.0)

    # Sample a PARTIALSAT / SAT child
    # PERF: Instead of recreating this categorical, each iteration, store it!
    cindex = rand(Categorical(transitionprobs))
    childid, q = children[cindex]
    child = node_from_id(t, childid)

    # Go a level deeper in tree
    depth += 1
    logq += log(q)
    window(:pre_child_expand, child, depth, length, child, niterations)

    if child.status == SAT
#       @show "Found SAT child"
      return child.data, logq
    elseif child.status == PARTIALSAT
#       @show "Found PARTIALSAT"
      node = child
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
  push!(boxes,box)
  println("Initial satisfying point found!, starting MH chain\n")

  naccepted = 0
  nsteps = 0
  while nsteps < max_iters
    nextbox, nextlogq = proposebox!(f,Y,X,t)
    nextlogp = logmeasure(nextbox)

    loga = nextlogp + logq - logp - nextlogq
    a = exp(loga)

    # MH accept/reject step
    if a >= 1 || rand() < a
      naccepted += 1
      box = nextbox
      logp = nextlogp
      logq = nextlogq
    end

    window(:post_accept,naccepted,nsteps,box,logp,logq)

    # Store current state every stepspersample-th timestep
    if nsteps % stepspersample == 0
      push!(boxes,box)
    end
    nsteps += 1
  end
  boxes
end

## Filters
## =======

mh_stats(naccepted, nsteps, box, logp, logq) =
  println("naccepted = $naccepted, nsteps = $(nsteps +1) ratio: $(naccepted/(nsteps+1))")

function check_bounds(niterations::Int, t::Tree)
  if niterations % 100 == 0
    if niterations > 40000
      error("Too many iterations")
    end
    if length(t.nodes) > 100000
      error("Tree is too big - will run out of memory")
    end
  end
end

function check_samples()
  af = fraction_sat(f,child.data,100)
  if niterations % 100 == 0 || af > 0
    @show af, depth
  end
  if af > 0 error("We got a point after $niterations niterations") end
end

register!(:post_accept, :mh_stats, mh_stats)
register!(:pre_refine, :check_bounds, check_bounds)
