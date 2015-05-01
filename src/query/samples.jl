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

# @doc "Point Sample the preimage" ->
function approx_pre_sample_bfs(Y::RandVar{Bool}, n::Int; pre_args...)
  Ysatsets, Ymixedsets = pre_bfs(Y, t, LazyOmega(); pre_args...)
  p = SamplePreimage(Ysatsets,Ymixedsets)
  samples = [rand(p) for i = 1:n]
end

# @doc "Point Sample the preimage" ->
function pre_sample_bfs(Y::RandVar{Bool}, n::Int; pre_args...)
  Ysatsets, Ymixedsets = pre_bfs(Y, t, LazyOmega(); pre_args...)
  p = SamplePreimage(Ysatsets,Ymixedsets)
  samples = [reject_sample(p,Y) for i = 1:n]
end

# @doc "Point Sample from X given Y" ->
function cond_sample_bfs{T}(X::RandVar{T}, Y::RandVar{Bool}, n::Int; pre_args...)
  T[call(X,s) for s in pre_sample_bfs(Y,n;pre_args...)]
end

cond_sample_bfs(X::RandVar, Y::RandVar{Bool}; pre_args...) = cond_sample_bfs(X,Y,1;pre_args...)[1]

## Statistics from samples
## =======================

# Conditional probability that X is true given Y is true
function cond_prob_bfs_sampled(X::RandVar{Bool}, Y::RandVar{Bool}; nsamples = 1000, pre_args...)
  samples = cond_sample_bfs(X, Y, nsamples; pre_args...)
  length(filter(x->x,samples))/length(samples)
end

# probability found using samples
function prob_sampled(X::RandVar; nsamples = 1000)
  ntrue = 0
  for i=1:nsamples if rand(X) ntrue += 1 end end
  ntrue/nsamples
end

## MH Sampling
## ===========
function cond_sample_mh(X::RandVar, Y::RandVar{Bool}, nsamples::Int; pre_args...)
  Ypresamples = pre_mh(Y,t,LazyOmega();max_iters = nsamples, pre_args...)
  r = rand(Ypresamples[1])
  [call(X, rand(i)) for i in Ypresamples]
end

function cond_prob_mh(X::RandVar{Bool}, Y::RandVar{Bool}, nsamples::Int; pre_args...)
  samples = cond_sample_mh(X, Y, nsamples; pre_args...)
  count(identity, samples) / length(samples)
end

## Expectation
## ===========
function sample_mean{T<:Real}(X::RandVar{T}; nsamples = 1000)
  mean(rand(X, nsamples))
end
