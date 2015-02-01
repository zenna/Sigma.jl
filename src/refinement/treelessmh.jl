## Parallel MH without Trees
## =========================

# This is a refinement algorithm like that found in mh.jl, except for the fact
# that it does not build a tree.  This also makes it easy for it to run in
# parallel.  The downside of not having a tree (I suspect) is that we may need to
# recompute things we've done already.  This is a minor loss if we gain a great deal
# in parallelism.

# Proposes a box using refinement (without storing tree). # f:X → Y
function proposebox_tl{D <: Domain}(f::Callable, Y, X::D;
                                    split::Function = weighted_partial_split, args...)
#   @show myid()
#   split = args[:split]
  niters = 0 ; depth = 0 ; logq = 0.0 # == log(1.0)
  A::D = X
  status = checksat(f,Y,X; args...)
  while niters <= 1E5
    if status == SAT
      window(:refinement_depth, depth)
      return A, logq
    elseif status == PARTIALSAT
      children::Vector{(Domain,Float64)} = split(A, depth)
      statuses = [checksat(f,Y,child[1]; args...) for child in children]
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

# Propose boxes in parallel
function propose_parallel_tl(f,Y,X,stack; ncores = 1, args...)
  ncores = min(ncores, nprocs())
  println("Using $ncores cores")
  if isempty(stack)
    spawns = [@spawn proposebox_tl(f,Y,X;args...) for i = 1:ncores]
    boxes = [fetch(s) for s in spawns]
    push!(stack,boxes...)
  end
  return pop!(stack)
end

# Uniform sample of subset of preimage of Y under f unioned with X.
# Uses metropolis hastings
function pre_tlmh{D <: Domain} (f::Callable, Y, X::D, niters; args...)
  boxes = D[]
  stack = (D,Float64)[] #For parallelism

  box, logq = proposebox_tl(f,Y,X; args...) # log for numercal stability
#   box, logq = propose_parallel_tl(f,Y,X,stack; args...)
  logp = logmeasure(box)
  push!(boxes,box)
  println("Initial satisfying point found!, starting MH chain\n")


  naccepted = 0; nsteps = 0
  while nsteps < niters - 1
    window(:start_loop,time_ns())
    nextbox, nextlogq = proposebox_tl(f,Y,X; args...)
#     nextbox, nextlogq = propose_parallel_tl(f,Y,X,stack; args...)
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

    window(:loop_stats, naccepted/niters, nsteps)
#     window(:post_accept,naccepted,nsteps,box,logp,logq)
    nsteps += 1
  end
  boxes
end

## Sampling
## ========
function cond_sample_tlmh(X::RandVar, Y::RandVar{Bool}, nsamples::Int; pre_args...)
  Ypresamples = pre_tlmh(Y,T,Omega(),nsamples; pre_args...)
  r = rand(Ypresamples[1])
  [call(X, rand(i)) for i in Ypresamples]
end

loop_stats(X...) = print(X)
register!(:loop_stats, :loop_stats, loop_stats)
