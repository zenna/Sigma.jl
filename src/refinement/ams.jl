## Abstract Metropolized Sampliing
## ===============================

"""Abstract Metropolized Sampliing samples events in preimage uniformly in
convergence of the Markov Chain.  This algorithm is useful for high dimensions"""
immutable AMS <: MCMCAlgorithm end

"Proposes a box by querying satisfiability solver multiple times"
function proposebox_tl{D <: Domain}(
    X::RandVar, box::D;
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
      children::Vector{Tuple{Domain,Float64}} = split(A, depth)
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

"Propose `n` boxes"
function propose_boxes{D <: Domain}(
    Y::SymbolicRandVar{Bool},
    init_box::D,
    nsamples::Integer;
    RandVarType::Type = default_randvar(),
    precision::Float64 = default_precision(),
    args...)

  Y_conv = convert(RandVarType{Bool}, Y)
  set_precision!(Y_conv, precision)
  println(Y_conv.ex)

  # DReal.opensmt_print_expr(Y_conv.ex.e)
  samples = Array{Tuple{D,Float64,Float64}}(nsamples)
  for i = 1:nsamples
    before = time_ns()
    samples[i] = preimage_proposal(Y_conv, init_box; args...)
    after = time_ns()
    lens(:sat_check, after-before)
  end
  cleanup(Y_conv)
  samples
end

## Parallel
## ========
"Generate a stack of `n` boxes in parallel"
function propose_boxes_parallel{D<:Domain}(
    Y::SymbolicRandVar,
    init_box::D,
    nsamples::Integer;
    ncores = nprocs() - 1,
    args...)

  println("Using $ncores cores to generate $nsamples")
  samplespercore = div(nsamples, ncores) + 1
  lst = [i for i = 1:ncores]
  g = _ -> propose_boxes(Y, init_box, samplespercore; args...)
  a = pmaplm(g, lst; ncores = min(nprocs(),ncores))
  samples = Tuple{D,Float64,Float64}[]
  for sampleset in a
    append!(samples, sampleset)
  end
  return samples
end

"From set of boxes run a markov chain in batch mode"
function run_chain{D <: Domain}(boxes::Vector{Tuple{D,Float64,Float64}})
  box, logq, prevolfrac = boxes[1]
  logp = logmeasure(box) + log(prevolfrac)
  chain = Array{D}(length(boxes))
  chain[1] = box

  naccepted = 0
  for i = 2:length(boxes)
    nextbox, nextlogq, prevolfrac = boxes[i]
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
    chain[i] = box
  end
  lens(:mh_ratio, naccepted/length(boxes))

  chain
end

"Uniform sample of subset of preimage of `Y` under `f` unioned with `X`."
function pre_mc(
    Y::SymbolicRandVar{Bool},
    nsamples::Integer,
    ::Type{AMS};
    RandVarType::Type = default_randvar(),
    parallel::Bool = true,
    args...)

  init_box = unit_box(LazyBox{Float64}, dims(Y))
  if parallel && nprocs() > 1
    boxes = propose_boxes_parallel(Y, init_box, nsamples; RandVarType = RandVarType, args...)
  else
    boxes = propose_boxes(Y, init_box, nsamples; RandVarType = RandVarType, args...)
  end

  run_chain(boxes)
end
