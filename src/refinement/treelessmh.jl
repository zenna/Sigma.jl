## Parallel MH without Trees
## =========================

# This is a refinement algorithm like that found in mh.jl, except for the fact
# that it does not build a tree.  This also makes it easy for it to run in
# parallel.  The downside of not having a tree (I suspect) is that we may need to
# recompute things we've done already.  This is a minor loss if we gain a great deal
# in parallelism.

# Adjust the proposal distribution
# frac_in_preimage is the fraction of the event which must be in the preimage
# Default 1 implies it must be a purely preimage sample
# Ohterwise, adjust_proposal will convert events that are TF to T if their
# percentage is greater than frac_in_preimage, determined by sampling
function adjust_proposal(statuses::Vector{SatStatus},weights::Vector{Float64},
                         children,f::Callable;
                         frac_in_preimage::Float64 = 0.01,
                         npre_tests::Int = 100, args...)
  if frac_in_preimage < 1.0
    # Compute preimage volume fractions
    prevolfracs = Array(Float64,length(children))
    for i = 1:length(children)
      if statuses[i] == T
        prevolfracs[i] = 1.0
      elseif statuses[i] == F
        prevolfracs[i] = 0.0
      else
        prevolfracs[i] = fraction_sat(f, children[i][1], npre_tests)
      end
    end

    @show prevolfracs
    @show statuses

    # Those with preimage vol fration higher than threshold are turned
    # to SAT
    newstatuses =
      [(statuses[i] == PARTIALSAT) && (prevolfracs[i] > frac_in_preimage) ? SAT : statuses[i] for i = 1:length(statuses)]
    newstatuses,weights, prevolfracs
  else
    statuses,weights, ones(Float64,length(statuses))
  end
end

## Stop functions
## ==============

# Proposes a box using refinement (without storing tree). # f:X → Y
function proposebox_tl{D <: Domain}(f::Callable, Y, X::D;
                                    split::Function = weighted_partial_split,
                                    maxdepth::Int = 1000,
                                    args...)
#   @show myid()
#   split = args[:split]
  niters = 0 ; depth = 0 ; logq = 0.0 # == log(1.0)
  prevolfrac = 1.0
  A::D = X
  status = checksat(f,Y,X; args...)
  while (niters <= 1E5) && (depth <= maxdepth)
#     @show status
    @show niters, depth
    if status == SAT
      window(:refinement_depth, depth)
        return A, logq, prevolfrac
    elseif status == PARTIALSAT
      children::Vector{(Domain,Float64)} = split(A, depth)
      statuses = [checksat(f,Y,child[1]; args...) for child in children]
#       @show statuses
#       @show children
      weights = pnormalize([statuses[i] == UNSAT ? 0.0 : children[i][2] for i = 1:length(children)])
      statuses, weights, prevolfracs = adjust_proposal(statuses, weights, children, f; args...)
      rand_index = rand(Categorical(weights))
#       println("Selecting Child - $rand_index")

      # Randomly Sample Child
      A = children[rand_index][1]
      status = statuses[rand_index]
      logq += log(weights[rand_index])
      prevolfrac = prevolfracs[rand_index]

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
  stack = (D,Float64,Float64)[] #For parallelism
  window(:start_loop,time_ns())
#   box, logq, prevolfrac = proposebox_tl(f,Y,X; args...) # log for numercal stability
  box, logq, prevolfrac = propose_parallel_tl(f,Y,X,stack; args...)
  logp = logmeasure(box) + log(prevolfrac)
  push!(boxes,box)
  println("Initial satisfying point found!, starting MH chain\n")


  naccepted = 0; nsteps = 0
  window(:start_loop,time_ns())
  while nsteps < niters - 1
#     nextbox, nextlogq, prevolfrac = proposebox_tl(f,Y,X; args...)
    nextbox, nextlogq, prevolfrac = propose_parallel_tl(f,Y,X,stack; args...)
    nextlogp = logmeasure(nextbox) + log(prevolfrac)

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
    window(:start_loop,time_ns())
    nsteps += 1
  end
  boxes
end

## Sampling
## ========
function rejection_presample(Y::RandVar, preimgevents; maxtries = 10000)
  local j; local preimgsample
  local k
  for j = 1:maxtries
    preimgsample =  rand(preimgevents)
    @show preimgevents
    @show preimgsample
    k = call(Y, preimgsample)
    k && break
  end
  @show j, k
  if j == maxtries error("Couldn't get sample from rejection") end
  preimgsample
end

# Sample nsample points from X conditioned on Y being true
function cond_sample_tlmh(X::RandVar, Y::RandVar{Bool}, nsamples::Int; pre_args...)
  Ypresamples = pre_tlmh(Y,T,Omega(),nsamples; pre_args...)
  samples = Array(rangetype(X),nsamples)
  for i = 1:length(Ypresamples)
    samples[i] = call(X,rejection_presample(Y,Ypresamples[i]))
  end
  samples
end

loop_stats(X...) = print(X)
register!(:loop_stats, :loop_stats, loop_stats)
