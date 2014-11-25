## Exact Sampling
## ==============
function cond_prob_bfs_sampled(X::RandVar, Y::RandVar{Bool}; nsamples = 1000)
  C = cond_bfs(X,Y)
  samples = [rand(C) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end

# probability found using samples
function prob_sampled(X::RandVar; nsamples = 1000)
  ntrue = 0
  for i=1:nsamples if rand(X) ntrue += 1 end end
  ntrue/nsamples
end

# conditional probability found using samples
function cond_prob_sampled_deep(X::RandVar, Y::RandVar{Bool}; nsamples = 1000)
  C = cond_deep(X,Y)
  samples = [rand(C) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end

## MH Sampling
## ===========
function cond_sample_mh(X::RandVar, Y::RandVar{Bool}, nsamples::Int; pre_args...)
  Ypresamples = pre_mh(Y,T,Omega();pre_args...)
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
