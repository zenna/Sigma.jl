## Parallel MH without Trees
## =========================

# This is a refinement algorithm like that found in mh.jl, except for the fact
# that it does not build a tree.  This also makes it easy for it to run in
# parallel.  The downside of not having a tree (I suspect) is that we may need to
# recompute things we've done already.  This is a minor loss if we gain a great deal
# in parallelism.

## ============================================================================

@doc """Abstract Independent Metropolis Sampliing samples events in preimage
  uniformly in convergence of the Markov Chain.
  This algorithm is useful for high dimensional problems""" ->
immutable AIM <: MCMCAlgorithm end

@doc "Proposes a box using refinement" ->
function proposebox_tl{D <: Domain}(X::RandVar, box::D;
                                    split::Function = weighted_partial_split,
                                    maxdepth::Int = 1000,
                                    precision::Float64 = DEFAULT_PREC,
                                    args...)
  niters = 0
  depth = 0
  logq = 0.0 # == log(1.0)
  prevolfrac = 1.0
  
  A::D = box
  lens(:refine,time_ns())
  image::AbstractBool = X(A)
  while (niters <= 1000) && (depth <= maxdepth)
    @show A
    if issmall(A, precision)
      lens(:depth, depth)
      lens(:refine,time_ns())
      return A, logq, 1.0  # Assume boxes are full
    # else if  isequal(image,t)
    #   lens(:proposing, depth=depth, niters=niters)
    #   return A, logq, 1.0  # Assume boxes are full
    elseif isequal(image, tf)
      @compat children::Vector{Tuple{Domain,Float64}} = split(A, depth)
      statuses = AbstractBool[]

      # Due to bug in dReal we're getting both a query and its negation unsat
      for child in children
        try
          child_status = X(child[1]; args...)
          push!(statuses,child_status)
        catch
          println("caught exception, both unsat")
          push!(statuses,f)
        end
      end
      weights = pnormalize([isequal(statuses[i],f) ? 0.0 : children[i][2] for i = 1:length(children)])

      # Sometimes all the children are false, even though parent is true, bug?
      if all([isequal(status,f) for status in statuses])
        lens(:depth, depth)
        lens(:refine,time_ns())
        return A, logq, 1.0
      end

      # Choose a random child
      # @show statuses
      # @show weights
      # @show A
      # @show children
      rand_index = rand(Categorical(weights))
      A = children[rand_index][1]
      status = statuses[rand_index]
      
      # Shouldn't go to empty children
      assert(!isequal(status,f))
      logq += log(weights[rand_index])
      
      depth += 1; niters += 1
      lens(:children_split, weights, children, depth, niters)
    elseif isequal(image, f) # Condition is unsatisfiable
      error("Cannot condition on unsatisfiable events")
    end
  end
  error("Unexpected Branch")
end

@doc "Uniform sample of subset of preimage of Y under f unioned with X." ->
function pre_mc{D <: Domain}(Y::RandVar{Bool},
                             init_box::D,
                             niters::Integer,
                             ::Type{AIM};
                             precision::Float64 = DEFAULT_PREC,
                             args...)
  @show "start of tml2"
  boxes = D[]
  box, logq, prevolfrac = proposebox_tl(Y,init_box; args...) # log for numercal stability
  logp = logmeasure(box) + log(prevolfrac)
  push!(boxes,box)

  println("Initial satisfying point found!, starting MH chain\n")
  naccepted = 0; nsteps = 0
  lens(:start_loop,time_ns())
  while nsteps < niters - 1
    nextbox, nextlogq, prevolfrac = proposebox_tl(Y,init_box; args...)
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


## Parallel 
# ## ========

# function genstack{D<:Domain}(Y::RandVar,box::D,nsamples::Int;ncores = 1,args...)
#   println("Using $ncores cores")
#   g = _ -> proposebox_tl(Y,box;args...)
#   lst = [i for i = 1:nsamples]
#   pmaplm(g, lst;ncores = min(nprocs(),ncores))
# end

# # Propose boxes in parallel
# function propose_pmap_tl{D<:Domain}(stack::Vector{Tuple{D,Float64,Float64}})
#   pop!(stack)
# end

# @doc "Parallely Uniform sample of subset of preimage of Y under f unioned with X." ->
# function pre_tlmh_parallel{D <: Domain, S <: DReal}(Y::RandVar{Bool}, init_box::D, niters::Integer,
#                   solver::Type{S}; precision::Float64 = DEFAULT_PREC, args...)
#   @show "start of parallel tml"
#   boxes = D[]
#   @compat stack::Vector{Tuple{D,Float64,Float64}} = genstack(Y,init_box,niters; args...)
#   box, logq, prevolfrac = propose_pmap_tl(stack) # log for numercal stability
#   logp = logmeasure(box) + log(prevolfrac)
#   push!(boxes,box)

#   println("Initial satisfying point found!, starting MH chain\n")
#   naccepted = 0; nsteps = 0
#   lens(:start_loop,time_ns())
#   while nsteps < niters - 1
#     nextbox, nextlogq, prevolfrac = propose_pmap_tl(stack)
#     nextlogp = logmeasure(nextbox) + log(prevolfrac)

#     loga = nextlogp + logq - logp - nextlogq
#     a = exp(loga)

#     # MH accept/reject step
#     if a >= 1 || rand() < a
#       naccepted += 1
#       box = nextbox
#       logp = nextlogp
#       logq = nextlogq
#     end
#     push!(boxes,box)

#     lens(:loop_stats, naccepted/niters, nsteps)
#     lens(:start_loop,time_ns())
#     nsteps += 1
#   end
#   boxes
# end