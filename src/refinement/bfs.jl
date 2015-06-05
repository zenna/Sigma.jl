## Preimage refinement by breadth first search
## ===========================================

function update_approx!{D<:Domain}(Y::RandVar{Bool}, box::D, satsets, mixedsets)
  children = mid_split(box)
  for child in children
    childsatstatus = Y(box)
    if isequal(childsatstatus, t)
      push!(satsets,child)
    elseif isequal(childsatstatus, tf)
      push!(mixedsets,child)
    end
  end
end

# Preimage of Y under F, unioned with X
#FIXME: Assumes X is PARTIALSAT
function pre_bfs{D <: Domain, S <: DReal}(Y::RandVar{Bool}, init_box::D, nsamples::Integer,
                  solver::Type{S}; precision::Float64 = DEFAULT_PREC, box_budget = 1000,
                  max_iters = 1000, args...)
  # Over and under approximation
  satsets = D[]
  local mixedsets
  satstatus = Y(init_box)
  if isequal(satstatus, t) return D[init_box],D[]
  elseif isequal(satstatus, f) return D[],D[]
  else mixedsets = D[init_box]
  end

  # debug
  # ratios1 = Float64[]
  # ratios2 = Float64[]

  # max iters is a hack to stop when we get very refined preimage
  # and we're no longer adding to our box_budget (just shrinking it)
  i = 0
  while length(mixedsets) + length(satsets) <= box_budget &&
        length(mixedsets) > 0 && i < max_iters
#     @show i
    # # debug
    # if i % 200 == 0
    #   push!(ratios1, length(mixedsets))
    #   push!(ratios2, length(satsets  ))
    # end

    box = shift!(mixedsets)
    update_approx!(Y,box,satsets,mixedsets)
    i += 1
  end

  # if i == max_iters println("Reached Max iterations - $i")
  # else println("Did $i iterations - max not reached") end
  satsets,mixedsets
end

# function categorical_sample(boxes::Vector)
#   weights = map(measure, boxes)
#   pweights = pnormalize(weights)
#   cat = Categorical(weights)
#   nsamples = 100000
#   for i = 1:nsamples
#   [rand(boxes[rand(cat))] for i = 1:nsamples]
# end

function pre_bfs(Y::RandVar{Bool}, nsamples::Int, solver::Type{DRealSolverBinary}; args...)
  box = LazyOmega(Float64)
  for dim in dims(Y)
    box[dim]
  end
  @show box
    println("Converting into dREAL Binary")
  Ydrealbinary = convert(DRealRandVarBinary{Bool}, Y)
  pre_bfs(Ydrealbinary, box, nsamples, solver; args...)
end

# Sampling

## Exact Sampling
## ==============

# @doc "A preimage representation efficient for sampling form" ->
type SamplePreimage
  both::Vector
  lastunderapprox::Int
  cat::Categorical

  function SamplePreimage(underapprox::Vector,overapprox::Vector)
    both = vcat(underapprox,overapprox)
    vols::Vector{Float64} = measures(both)
    pnormalize!(vols)
    c = Categorical(vols, Distributions.NoArgCheck())
    new(both,length(underapprox),c)
  end
end

# @doc "Point sample from preimage - may be invalid point due to approximations" ->
function rand(P::SamplePreimage)
  omega = P.both[rand(P.cat)]
  sample = rand(omega)
end

# @doc "Do refined rejection sampling from preimage" ->
function reject_sample(p::SamplePreimage, Y::RandVar{Bool}; maxtries = 1E7)
  nrejected = 0
  ntried = 0
  for i = 1:maxtries
    sample = rand(p)
    if call(Y,sample) return sample end
  end
  error("Could not get sample in $maxtries tries")
end

# # @doc "Point Sample the preimage" ->
# function approx_pre_sample_bfs(Y::RandVar{Bool}, n::Int; pre_args...)
#   Ysatsets, Ymixedsets = pre_bfs(Y, t, LazyOmega(); pre_args...)
#   p = SamplePreimage(Ysatsets,Ymixedsets)
#   samples = [rand(p) for i = 1:n]
# end

# @doc "Point Sample the preimage" ->
function pre_sample_bfs(Y::RandVar{Bool}, nsamples::Int, solver::Type{DRealSolverBinary}; args...)
  Ysatsets, Ymixedsets = pre_bfs(Y, nsamples, solver; args...)
  p = SamplePreimage(Ysatsets,Ymixedsets)
  samples = [reject_sample(p,Y) for i = 1:nsamples]
end

function rand_bfs(X::AllRandVars,Y::RandVar{Bool},nsamples::Int)
  pre_samples = pre_sample_bfs(Y, nsamples, DRealSolverBinary)
  X_fn = lambda(X)
  [X_fn(pre_sample) for pre_sample in pre_samples]
end