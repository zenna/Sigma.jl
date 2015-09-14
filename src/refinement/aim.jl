## Abstract Independent Metropolis Sampliing
## ==========================================

"""Abstract Independent Metropolis Sampliing samples events in preimage
  uniformly in convergence of the Markov Chain.
  This algorithm is useful for high dimensional problems"""
immutable AIM <: MCMCAlgorithm end

"Proposes a box using refinement"
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
  @show image::AbstractBool = call(X, A)
  while (niters <= 1000) && (depth <= maxdepth)
    @show depth
    @show measure(A)
    A, image
    if issmall(A, precision)
      lens(:depth, depth)
      lens(:refine,time_ns())
      println("Got Sample")
      return A, logq, 1.0  # Assume boxes are full
    # else if  isequal(image,t)
    #   lens(:proposing, depth=depth, niters=niters)
    #   return A, logq, 1.0  # Assume boxes are full
    elseif isequal(image, tf)
      @compat children::Vector{Tuple{Domain,Float64}} = split(A, depth)
      statuses = AbstractBool[]

      # Due to bug in DReal we're getting both a query and its negation unsat
      for child in children
        try
          child_status = call(X, child[1])
          push!(statuses,child_status)
        catch e
          rethrow(e)
          println("caught exception $e")
          println(A)
          println(X)
          [println(child) for child in children]
          push!(statuses,f)
        end
      end
      weights = pnormalize([isequal(statuses[i],f) ? 0.0 : children[i][2] for i = 1:length(children)])

      # Sometimes all the children are false, even thoughrand pnarent is true, bug?
      if all([isequal(status,f) for status in statuses])
        @show "Found Bug $depth"
        @show statuses
        @show children
        @show A
        @show typeof(X)
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

"Get boxes but faster"
function propose_integrated{D <: Domain}(
    Y::DRealRandVar{Bool},
    init_box::D; args...)

  DReal.push_ctx!(Y.ctx)

  ## Define subset (box) of Omega using assertions
  for (symb, var) in Y.sym_to_var
    interval = bounds(symb, init_box)
    add_bound_constraints!(Y.ctx, var, interval.l, interval. u)
  end
  DReal.add!(Y.ctx, Y.ex)

  issat = DReal.is_satisfiable()

  !issat && error("Cannot condition on unsatisfiable events")

  A = LazyBox(Float64) #FIXME Float64 too speific?
  for (symb, var) in Y.sym_to_var
    A[symb.dim] = model(Y.ctx, var)
  end

  # I believe all the boxes are going to have the same size, so assuming that's true
  # we can just return some constant for the size.

  # As for the box itself, we need to return an abstract omega.
  dummy_ex = first(Y.sym_to_var)[2]
  logq = DReal.opensmt_get_model_logprob(Y.ctx.ctx, dummy_ex.e)
  DReal.pop_ctx!(Y.ctx)
  A, logq, 1.0
end

"Propose `n` boxes"
function propose_integrated_n{D <: Domain}(
    Y::SymbolicRandVar{Bool},
    init_box::D;
    nsamples::Integer = 5,
    args...)
  YDReal = convert(DRealRandVar{Bool}, Y)
  samples = Array(Tuple{D,Float64,Float64}, nsamples)
  for i = 1:nsamples
    before = time_ns()
    @time samples[i] = propose_integrated(YDReal, init_box; args...)
    after = time_ns()
    lens(:sat_check, after-before)
  end
  DReal.delete_ctx!(YDReal.ctx)
  samples
end

"Uniform sample of subset of preimage of `Y` under `f` unioned with `X`."
function pre_mc{D <: Domain}(Y::RandVar{Bool},
                             init_box::D,
                             niters::Integer,
                             ::Type{AIM};
                             propose_box = propose_integrated,
                             precision::Float64 = DEFAULT_PREC,
                             parallel::Bool = false,
                             args...)

  set_precision!(Y, precision)

  @compat stack::Vector{Tuple{D,Float64,Float64}} = parallel ?
    genstack(Y,init_box,niters; args...) : Tuple{D,Float64,Float64}[]

  boxes = D[]
  box, logq, prevolfrac = parallel ? propose_pmap_tl(stack) :
                                     propose_box(Y,init_box; args...)
  logp = logmeasure(box) + log(prevolfrac)
  push!(boxes, box)

  @show length(stack)

  println("Initial satisfying point found!, starting MH chain\n")
  naccepted = 0; nsteps = 0
  lens(:start_loop,time_ns())

  while nsteps < niters - 1
    println("Drawn $(nsteps+1) samples")
    nextbox, nextlogq, prevolfrac = parallel ? propose_pmap_tl(stack) :
                                               propose_box(Y,init_box; args...)
    nextlogp = logmeasure(nextbox) + log(prevolfrac)

    loga = nextlogp + logq - logp - nextlogq
    a = exp(loga)

    @show nextlogq

    @show nextbox
    # MH accept/reject step
    if a >= 1 || rand() < a
      naccepted += 1
      box = nextbox
      logp = nextlogp
      logq = nextlogq
    end
    push!(boxes,box)

    lens(:start_loop,time_ns())
    nsteps += 1
  end
  lens(:post_loop, naccepted/niters)

  boxes
end


## Parallel
## ========
# Generate a stack of boxes
function genstack{D<:Domain}(
    Y::RandVar,
    box::D,
    nsamples::Int;
    ncores = 2,
    propose_box = propose_integrated_n,
    args...)
  println("Using $ncores cores to generate $nsamples")
  samplespercore = div(nsamples,ncores)
  lst = [i for i = 1:ncores]
  g = _ -> propose_box(Y,box; nsamples = samplespercore, args...)
  a = pmaplm(g, lst; ncores = min(nprocs(),ncores))
  samples = Tuple{D,Float64,Float64}[]
  for sampleset in a
    append!(samples, sampleset)
  end
  return samples
end

# Propose boxes in parallel
function propose_pmap_tl{D<:Domain}(stack::Vector{@compat Tuple{D,Float64,Float64}})
  pop!(stack)
end
