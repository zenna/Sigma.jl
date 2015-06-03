## TLMH Sampling
## =============
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

# Generate random sample from distribution of X
function rand{T}(X::RandVar{T})
  func = lambda(X)
  func(LazyRandomVector(Float64))::T
end

# Generate n random samples from distribution of X
function rand{T}(X::RandVar{T}, nsamples::Int)
  func = lambda(X)
  T[func(LazyRandomVector(Float64)) for i = 1:nsamples]
end

function lambda{T}(XS::PureRandArray{T,2})
  X_fns = map(lambda,XS.array)
  ω -> [X_fns[i,j](ω) for i = 1:size(XS,1), j = 1:size(XS,2)]
end

AllRandVars = Union(RandVar, PureRandArray)
function rand(randvars::Tuple{AllRandVars,AllRandVars,AllRandVars}, Y::RandVar{Bool}, nsamples::Int)
  funcs = map(lambda, randvars)
  preimage_boxes = pre_tlmh(Y, nsamples)
  preimage_points = [rand(box) for box in preimage_boxes]
  warn("Sampling points is wrong (biased towards smaller regions)")
  ([funcs[1](point) for point in preimage_points],
   [funcs[2](point) for point in preimage_points],
   [funcs[3](point) for point in preimage_points])
end

call(X::RandVar,ω::Omega) = lambda(X)(ω)


rand{T,N}(X::PureRandArray{T,N}, Y::RandVar{Bool}, nsamples::Int) = cond_sample_tlmh(X,Y,nsamples)
rand{T}(X::RandVar{T}, Y::RandVar{Bool}, nsamples::Int) = cond_sample_tlmh(X,Y,nsamples)
rand{T}(X::RandVar{T}, Y::RandVar{Bool}) = cond_sample_tlmh(X,Y,1)[1]
