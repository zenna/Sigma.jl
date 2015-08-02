## Expectation
## ===========
function sample_mean{T<:Real}(X::RandVar{T}; nsamples = 1000)
  mean(rand(X, nsamples))
end

# probability found using samples
function prob_sampled(X::RandVar; nsamples = 1000)
  ntrue = 0
  for i=1:nsamples if rand(X) ntrue += 1 end end
  ntrue/nsamples
end