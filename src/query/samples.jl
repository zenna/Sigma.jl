## TLMH Sampling
## =============

@doc "Generate an unconditioned random sample from distribution of X" ->
function rand{T}(X::RandVar{T})
  func = lambda(X)
  func(LazyRandomVector(Float64))::T
end

@doc "Generate n unconditioned random samples from distribution of X" ->
function rand{T}(X::RandVar{T}, nsamples::Int)
  func = lambda(X)
  T[func(LazyRandomVector(Float64)) for i = 1:nsamples]
end

function cond_sample_tlmh{T}(X::RandVar{T}, Y::RandVar{Bool}, nsamples::Int)
  preimage_boxes = pre_tlmh(Y, nsamples)
  warn("Sampling points is wrong (biased towards smaller regions)")
  preimage_points = [rand(box) for box in preimage_boxes]
  X_fn = lambda(X)
  T[X_fn(point) for point in preimage_points]
end

@doc "Sample points from an Array X given Y is true" ->
function cond_sample_tlmh{T,N}(X::PureRandArray{T,N}, Y::RandVar{Bool}, nsamples::Int)
  preimage_boxes = pre_tlmh(Y, nsamples)
  warn("Sampling points is wrong (biased towards smaller regions)")
  preimage_points = [rand(box) for box in preimage_boxes]
  X_fns = map(x->lambda(x),X.array)
  Array{T,N}[map(fn->fn(point),X_fns) for point in preimage_points]
end

@doc "Sample points from A tuple `randvars` of any random variables given Y is true" ->
function rand(randvars::Tuple{AllRandVars,AllRandVars,AllRandVars}, Y::RandVar{Bool}, nsamples::Int)
  funcs = map(lambda, randvars)
  preimage_boxes = pre_tlmh(Y, nsamples)
  preimage_points = [rand(box) for box in preimage_boxes]
  warn("Sampling points is wrong (biased towards smaller regions)")
  ([funcs[1](point) for point in preimage_points],
   [funcs[2](point) for point in preimage_points],
   [funcs[3](point) for point in preimage_points])
end

rand{T,N}(X::PureRandArray{T,N}, Y::RandVar{Bool}, nsamples::Int) = cond_sample_tlmh(X,Y,nsamples)
rand{T}(X::RandVar{T}, Y::RandVar{Bool}, nsamples::Int) = cond_sample_tlmh(X,Y,nsamples)
rand{T}(X::RandVar{T}, Y::RandVar{Bool}) = cond_sample_tlmh(X,Y,1)[1]

## Model
## =====

@doc """Generates a 'model' from X given that Y is true, a model is like a sample
  except that it does not follow any wel ldefined distribution""" ->
function preimage_model(Y::DRealRandVar{Bool})
  dreal_model = dReal.model(Y)
  !is_satisfiable(Y.ctx) && "Cannot draw model from unsatisfiable condition"
  preimage_sample = LazyBox(Float64)
  for (dim,var) in Y.dimToVar
    preimage_sample[dim] = model(Y.ctx,var)
  end
  preimage_sample
end

function model2(X::RandVar, Y::DRealRandVar{Bool})
  push_ctx!(Y.ctx)
  dReal.add!(Y.ctx,Y.ex)
  println("Checking Satisfiability")
  issat = is_satisfiable(Y.ctx)
  if !issat
    pop_ctx!(Y.ctx)
    error("Cannot draw model from unsatisfiable condition")
  end
  println("model_is_satisfiable")
  preimage_sample = LazyBox(Float64)
  for (dim,var) in Y.dimtovar
    preimage_sample[dim] = dReal.model(Y.ctx,var)
  end
  @show preimage_sample
  pop_ctx!(Y.ctx)
  call(X,rand(preimage_sample))
end

@doc """Generates a 'model' from X given that Y is true, a model is like a sample
  except that it does not follow any wel ldefined distribution""" ->
function model(X::RandVar, Y::RandVar{Bool})
  Ydreal::DRealRandVar = convert(DRealRandVar{Bool}, Y)
  model2(X,Ydreal)
end
