## Refine Reweight Restart Algorithm
## ========================

## TODO
## What if we get imprecision
## What about sampling?

# A conceptual question is whether the output of this should be samples
# or abstract samples
# In line with the single responsibility principle perhaps we should let it be
# abstract samples, and if we want concrete samples let this be done by another process.

# This refinement algorithm constructs a tree, as in mh
# However, when an UNSAT node is found we:
# 1. block of that node reweight the edges
# 2. reweight the edges such that the blocking does not affect leaf probabilities
# 3. restart from the top

# Stop if too much time/memory used
# TODO
function shouldstop(niterations, t::WeightedTree)
  if niterations % 1 == 0
    if niterations > 1000000
      warn("Too many iterations - $niterations")
      return true
    end
    if length(t.nodes) > 1000000
      warn("Tree is too big $(length(t.nodes)) - will run out of memory")
      return true
    end
  end
  return false
end

function updatepathnodes!(path::Vector{(Node, Int)}, t::WeightedTree,
                          weightloss::Float64)
  # Iterate backwards from end of path
#   println("Deducting $weightloss")
  logruntotal = log(weightloss)
  for i = length(path):-1:1
    p = path[i]
    parent = p[1]
    child::NodeWeight = getchild(t,parent, p[2])
    logruntotal = log(getweight(child)) + logruntotal
    newweight = getweight(child) - exp(logruntotal)
    t.children[parent.id][p[2]] = (child[1],newweight)
    normalize_children!(t, parent)
  end
end

function randchild(t::Tree, children)
  transitionprobs = Float64[child[2] for child in children]
  @assert isapprox(sum(transitionprobs),1.0)
  cindex = rand(Categorical(transitionprobs))
end

function add_children!(t::WeightedTree, node::Node, children::Vector{(Node, Float64)})
  for (child, weight) in children
    add_child!(t, child, node.id, weight)
  end
end

function sort_children(f::Callable, Y, t::WeightedTree, node::Node, depth::Int, split::Function)
  children::Vector{(Domain,Float64)} = split(node.data, depth)
#   @show length(children)
  unsatnodes = (Node,Float64)[]
  psatnodes = (Node,Float64)[]

  # Weights should sum to 1
  @assert sum([child[2] for child in children]) == 1.0

  for i = 1:length(children)
    #FIXME USELESS 0 index NODE is CODEMSELL
    childdata, weight = children[i]
    satstatus = checksat(f,Y,childdata)
    childnode = Node(0,satstatus,childdata)
    if satstatus == UNSAT
      push!(unsatnodes, (childnode, weight))
    else
      push!(psatnodes, (childnode, weight))
    end
  end
  unsatnodes, psatnodes
end

function normalize_weights(nws::Vector{(Node, Float64)})
  weights = [nw[2] for nw in nws ]
  pnormalize!(weights)
  [(nws[i][1], weights[i]) for i = 1:length(nws)]
end

function refinetree!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree,
                                  split::Function = weighted_mid_split)
  ## Initialisation
  niterations = 0
  nrestarts = 0
  @label restart
#   @show "Restarting"
  node::Node{D} = root(t)
  depth = 0
  logp = 0.0 # == log(1.0)
  path = (Node, Int)[] # Current path in refinement

  # Start refinement
  @label start
#   @show "Starting, $niterations"
  niterations += 1

  ## Should we stop?
  shouldstop(niterations, t) && return node

  if node.status == SAT
    @show "stopped at initial sat"
    return tree, leaves
  elseif node.status == PARTIALSAT
    # Add children if none there
    if !has_children(t,node)
      unsatnodes, psatnodes = sort_children(f, Y, t, node, depth, split)
      children::Vector{(Node,Float64)} = normalize_weights(psatnodes)
      if isempty(children)
        error("No children due to imprecision")
      else
        add_children!(t,node,children)#TODO
      end

      # There are UNSAT children, reweight and restart
      if length(unsatnodes) > 0
        # Total mass in unsates must be deducted
        weightloss = sum([nw[2] for nw in unsatnodes])
        updatepathnodes!(path,t, weightloss)
        nrestarts += 1
        @goto restart
      end
    end

    # Sample a child
    thechildren = getchildren(t,node)
    childindex = randchild(t,thechildren)
    childid::Int, weight::Float64 = thechildren[childindex]
    child = node_from_id(t,childid)
    if child.status == SAT
      @show nrestarts
      return child
    elseif child.status == PARTIALSAT
      push!(path, (node,childindex))
      node = child
      depth += 1
#       @show depth
      @goto start
    elseif child.status == UNSAT
      @unexpected
    end
  end
end

# Output is a set of abstractions
# f:X → Y
function pre_rrr{D <: Domain}(f::Callable, Y, X::D; max_iters = 100)
  # Construct tree with root node as preimage
  t = WeightedTree(Node(1, checksat(f,Y,X), X))
  boxes = D[]

  nsteps = 0
  while nsteps < max_iters
    refinetree!(f, Y, X, t)
    nsteps += 1
  end
  t
end

# ## Example
# ## ======
# X = uniform(0,1)
# Y = X > 0.5

# pre_rrr(Y, T, LazyOmega(), max_iters = 2)
