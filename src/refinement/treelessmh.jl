## Parallel MH without Trees
## =========================

# This is a refinement algorithm like that found in mh.jl, except for the fact
# that it does not build a tree.  This also makes it easy for it to run in
# parallel.  The downside of not having a tree (I suspect) is that we may need to
# recompute things we've done already.  This is a minor loss if we gain a great deal
# in parallelism.

## ============================================================================

# Adjust the proposal distribution
# frac_in_preimage is the fraction of the event which must be in the preimage
# Default 1 implies it must be a purely preimage sample
# Ohterwise, adjust_proposal will convert events that are t to f if their
# percentage is greater than frac_in_preimage, determined by sampling
# function adjust_proposal(statuses::Vector{AbstractBool},weights::Vector{Float64},
#                          children,f::Callable;
#                          frac_in_preimage::Float64 = 0.01,
#                          npre_tests::Int = 100, args...)
#   if frac_in_preimage < 1.0
#     # Compute preimage volume fractions
#     prevolfracs = Array(Float64,length(children))
#     for i = 1:length(children)
#       if statuses[i] == SAT
#         prevolfracs[i] = 1.0
#       elseif statuses[i] == UNSAT
#         prevolfracs[i] = 0.0
#       else
#         prevolfracs[i] = fraction_sat(f, children[i][1], npre_tests)
#       end
#     end

# #     @show prevolfracs
# #     @show statuses

#     # Those with preimage vol fration higher than threshold are turned
#     # to SAT
#     newstatuses =
#       [(statuses[i] == PARTIALSAT) && (prevolfracs[i] > frac_in_preimage) ? SAT : statuses[i] for i = 1:length(statuses)]
#     newstatuses,weights, prevolfracs
#   else
#     statuses,weights, ones(Float64,length(statuses))
#   end
# end


function issmall(box::Boxes, precision::Float64)
  for dim in dims(box)
    (measure(box[dim]) > precision)&& return false
  end
  return true
end

# Proposes a box using refinement (without storing tree). # f:X → Y
function proposebox_tl{D <: Domain}(X::RandVar, box::D;
                                    split::Function = weighted_partial_split,
                                    maxdepth::Int = 1000,
                                    precision::Float64 = 0.001,
                                    args...)
#   @show myid()
#   split = args[:split]

  niters = 0 ; depth = 0 ; logq = 0.0 # == log(1.0)
  prevolfrac = 1.0
  @show box
  A::D = box
  image::AbstractBool = X(A; args...)
  while (niters <= 10) && (depth <= maxdepth)
    @show A
#     @show status
    # @show niters, depth
    if @show issmall(A, precision)
       assert(!isequal(X(A),f))
       return A, logq, prevolfrac
    elseif isequal(image,t)
#       lens(:refinement_depth, depth)
      return A, logq, prevolfrac
    elseif isequal(image, tf)
      children::Vector{Tuple{Domain,Float64}} = split(A, depth)
      statuses = [X(child[1]; args...) for child in children]
      @show statuses
#       @show children
      weights = pnormalize([isequal(statuses[i],f) ? 0.0 : children[i][2] for i = 1:length(children)])
      # statuses, weights, prevolfracs = adjust_proposal(statuses, weights, children, f; args...)
      rand_index = rand(Categorical(weights))
#       println("Selecting Child - $rand_index")

      # Randomly Sample Child
      A = children[rand_index][1]
      status = statuses[rand_index]
      assert(!isequal(status,f))
      logq += log(weights[rand_index])
#       prevolfrac = prevolfracs[rand_index]
      prevolfrac = 1

      depth += 1; niters += 1
    elseif isequal(image, f) # Condition is unsatisfiable
      error("Cannot condition on unsatisfiable events")
    end
  end
  error("Unexpected Branch")
end

# # Propose boxes in parallel
# function propose_parallel_tl(f,Y,X,stack; ncores = 1, args...)
#   ncores = min(ncores, nprocs())
#   println("Using $ncores cores")
#   if isempty(stack)
#     spawns = [@spawn proposebox_tl(f,Y,X;args...) for i = 1:ncores]
#     boxes = [fetch(s) for s in spawns]
#     push!(stack,boxes...)
#   end
#   return pop!(stack)
# end

# function genstack(f,Y,X,nsamples;ncores = 1,args...)
#   println("Using $ncores cores")
#   g = _ -> proposebox_tl(f,Y,X;args...)
#   lst = [i for i = 1:nsamples]
#   pmaplm(g, lst;ncores = min(nprocs(),ncores))
# end

# # Propose boxes in parallel
# function propose_pmap_tl(f,Y,X,stack; ncores = 1, args...)
#   pop!(stack)
# end

# @doc "Uniform sample of subset of preimage of Y under f unioned with X." ->
function pre_tlmh{D <: Domain}(Y::RandVar{Bool}, init_box::D, niters::Integer; precision::Float64 = 0.001, args...)
  boxes = D[]
  # stack = (D,Float64,Float64)[] #For parallelism
  # stack::Vector{(D,Float64,Float64)} = genstack(f,Y,X,niters;args...)
  # lens(:start_loop,time_ns())
  @show "start of tml2"
  box, logq, prevolfrac = proposebox_tl(Y,init_box; args...) # log for numercal stability
#   box, logq, prevolfrac = propose_pmap_tl(f,Y,X,stack; args...)
  logp = logmeasure(box) + log(prevolfrac)
  push!(boxes,box)

  println("Initial satisfying point found!, starting MH chain\n")
  naccepted = 0; nsteps = 0
  lens(:start_loop,time_ns())
  while nsteps < niters - 1
    nextbox, nextlogq, prevolfrac = proposebox_tl(Y,init_box; args...)
    # nextbox, nextlogq, prevolfrac = propose_pmap_tl(f,Y,X,stack; args...)
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

    lens(:loop_stats, naccepted/niters, nsteps)
    lens(:start_loop,time_ns())
    nsteps += 1
  end
  boxes
end

function pre_tlmh2(Y::RandVar{Bool}, niters::Int; args...)
  box = LazyOmega(Float64)
  for dim in dims(Y)
    box[dim]
  end
  @show box
  Ydreal::DRealRandVar = convert(DRealRandVar{Bool}, Y)
  pre_tlmh(Ydreal, box, niters)
end


# ## Sampling
# ## ========
# function rejection_presample(Y::RandVar, preimgevents; maxtries = 10000)
#   local j; local preimgsample
#   local k
#   for j = 1:maxtries
#     preimgsample =  rand(preimgevents)
#     k = call(Y, preimgsample)
#     k && break
#   end
#   if j == maxtries error("Couldn't get sample from rejection") end
#   preimgsample
# end

# # Sample nsample points from X conditioned on Y being true
# function cond_sample_tlmh(X::RandVar, Y::RandVar{Bool}, nsamples::Int; pre_args...)
#   Ypresamples = pre_tlmh(Y,t,LazyOmega(),nsamples; pre_args...)
#   samples = Array(rangetype(X),nsamples)
#   for i = 1:length(Ypresamples)
#     samples[i] = call(X,rejection_presample(Y,Ypresamples[i]))
#   end
#   lens(:samples, samples)
#   samples
# end
