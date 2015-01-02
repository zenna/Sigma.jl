## Refine Reweight Restart Algorithm
## ========================

# Remove all children
function remove_unsat_children!(t::WeightedTree,node::Node)
  thechildren = getchildren(t,node)
  weightloss = 0.0
  nunsat = 0
  for i = 1:length(thechildren)
    childid, weight = thechildren[i]
    if t.nodes[childid].status == UNSAT
      # Found unsat node, set its weight to zero
      weightloss += weight
      nunsat += 1
      t.children[node.id][i] = (childid, 0.0)
    end
  end
#   println("$nunsat out of $(length(thechildren)) UNSAT")
  return weightloss
end

function narrow_refinetree!{D <: Domain}(f::Callable, Y, X::D, t::WeightedTree,
                                  split::Function = weighted_partial_split)
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
    # No need to evaluate sat of all the children
    # Even if we do, sample one, if its UNSAT, then reweigh all the children
    if !has_children(t,node)
      unsatnodes, psatnodes = sort_children(f, Y, t, node, depth, split)
      children::Vector{(Node,Float64)} = normalize_weights(psatnodes)
      if isempty(children)
        error("No children due to imprecision")
      else
        add_children!(t,node,psatnodes)
        add_children!(t,node,unsatnodes)
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
      weightloss = remove_unsat_children!(t,node)
#       @show weightloss
      normalize_children!(t,node)
      # There are UNSAT children, reweight and restart
      # Total mass in unsates must be deducted
      updatepathnodes!(path,t, weightloss)
      nrestarts += 1
#       @show "Restarting $nrestarts"
      @goto restart
    end
  end
end

# Output is a set of abstractions
# f:X → Y
function pre_nrrr{D <: Domain}(f::Callable, Y, X::D; max_iters = 100)
  # Construct tree with root node as preimage
  t = WeightedTree(Node(1, checksat(f,Y,X), X))
  boxes = D[]

  nsteps = 0
  while nsteps < max_iters
    println("MH Iteration: $(length(t.nodes))")
    narrow_refinetree!(f, Y, X, t)
    nsteps += 1
  end
  t
end