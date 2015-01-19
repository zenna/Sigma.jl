## Parallel MH without Trees
## =========================

# This is a refinement algorithm like that found in mh.jl, except for the fact
# that it does not build a tree.  This also makes it easy for it to run in
# parallel.  The downside of not having a tree (I suspect) is that we may need to
# recompute things we've done already.  This is a minor loss if we gain a great deal
# in parallelism.

# Proposes a box using refinement (without storing tree). # f:X → Y
function proposebox_tl{D <: Domain}(f::Callable, Y, X::D, split::Function = rand_partial_split)
  @show myid()
  niters = 0 ; depth = 0 ; logq = 0.0 # == log(1.0)
  A::D = X
  status = checksat(f,Y,X)
  while niters <= 1E5
    if status == SAT
      return A, logq
    elseif status == PARTIALSAT
      children::Vector{(Domain,Float64)} = split(A, depth)
      statuses = [checksat(f,Y,child[1]) for child in children]
      weights = pnormalize([statuses[i] == UNSAT ? 0.0 : children[i][2] for i = 1:length(children)])
      rand_index = rand(Categorical(weights))

      # Randomly Sample Child
      A = children[rand_index][1]
      status = statuses[rand_index]
      logq += log(weights[rand_index])

      depth += 1; niters += 1
    elseif status == UNSAT # Condition is unsatisfiable
      error("Cannot condition on unsatisfiable events")
    end
  end
  @unexpected
end

function propose_parallel_tl(f,Y,X,stack)
  if isempty(stack)
    spawns = [@spawn proposebox_tl(f,Y,X) for i = 1:nprocs()]
    boxes = [fetch(s) for s in spawns]
    push!(stack,boxes...)
  end
  return pop!(stack)
end

# Uniform sample of subset of preimage of Y under f unioned with X.
# Uses metropolis hastings
function pre_tlmh{D <: Domain} (f::Callable, Y, X::D; niters = 100)
  boxes = D[]
  box, logq = proposebox_tl(f,Y,X) # log for numercal stability
  logp = logmeasure(box)
  push!(boxes,box)
  println("Initial satisfying point found!, starting MH chain\n")

  stack = (D,Float64)[] #For parallelism

  naccepted = 0; nsteps = 0
  while nsteps < niters
#     nextbox, nextlogq = proposebox_tl(f,Y,X)
    nextbox, nextlogq = propose_parallel_tl(f,Y,X,stack)
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
    push!(boxes,box)

#     window(:post_accept,naccepted,nsteps,box,logp,logq)
    nsteps += 1
  end
  boxes
end
