## Unconditional Sampling
## ======================

@doc "Generate an unconditioned random sample from X" ->
function rand{T}(X::RandVar{T})
  func = lambda(X)
  func(LazyRandomVector(Float64))::T
end

@doc "Generate `nsamples` unconditioned random samples from distribution of X" ->
function rand{T}(X::RandVar{T}, nsamples::Int)
  func = lambda(X)
  T[func(LazyRandomVector(Float64)) for i = 1:nsamples]
end

## Conditional Sampling
## ====================

function rand{T, S<:Solver}(X::RandVar{T}, Y::RandVar{Bool}, nsamples::Int,
                            algo::Function = pre_tlmh, solver::Type{S} = DRealSolver)
  # Sample boxes in preimage of Y
  preimage_boxes = algo(Y, nsamples, solver)
  warn("Sampling points is wrong (biased towards smaller regions)")

  # Get uniformly distributed points within these preimages
  @show preimage_boxes
  preimage_points = [rand(box) for box in preimage_boxes]

  # Evaluate X(ω) for each point in preimage of Y
  println("About to lambarise")
  X_fn = lambda(X)
  T[X_fn(point) for point in preimage_points]
end

@doc "Sample points from an Array X given Y is true" ->
function rand{T,N,S<:Solver}(X::PureRandArray{T,N}, Y::RandVar{Bool}, nsamples::Int,
                   algo::Function = pre_tlmh, solver::Type{S} = DRealSolver)
  preimage_boxes = algo(Y, nsamples, solver)
  warn("Sampling points is wrong (biased towards smaller regions)")
  preimage_points = [rand(box) for box in preimage_boxes]
  X_fns = map(x->lambda(x),X.array)
  Array{T,N}[map(fn->fn(point),X_fns) for point in preimage_points]
end

# @doc "Sample points from A tuple `randvars` of any random variables given Y is true" ->
# function rand(randvars::Tuple{AllRandVars,AllRandVars,AllRandVars}, Y::RandVar{Bool}, nsamples::Int)
#   funcs = map(lambda, randvars)
#   preimage_boxes = pre_tlmh(Y, nsamples)
#   preimage_points = [rand(box) for box in preimage_boxes]
#   warn("Sampling points is wrong (biased towards smaller regions)")
#   ([funcs[1](point) for point in preimage_points],
#    [funcs[2](point) for point in preimage_points],
#    [funcs[3](point) for point in preimage_points])
# end
