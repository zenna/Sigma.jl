## Exact Sampling
## ==============

cond_sample_bfs(X::RandVar, Y::RandVar{Bool}; pre_args...) = rand(cond_bfs(X,Y,pre_args...))

function cond_sample_bfs(X::RandVar, Y::RandVar{Bool}, n::Int; pre_args...)
  C = cond_bfs(X,Y; pre_args...)
  samples = [rand(C) for i=1:n]
end

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
  Ypresamples = pre_mh(Y,T,Omega();max_iters = nsamples, pre_args...)
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
