using Sigma

prob_tagged = 0.2
is_tagged = flip(prob_tagged)
λ = 0.5

spike_train  = RandArray(Float64, 100)
spike_train[1] = exponential(λ)
for i = 2:100
  spike_train[i] = exponential(λ) + spike_train[i-1]
end

light_onset = 100.0

if is_tagged
  ##
##


prob_tagged = 0.2
is_tagged = flip(prob_tagged)

λ = uniform(0.5, 0.6)

λ2 = ifelse(is_tagged,
          λ, 
          λ*2)

spike1 = exponential(λ2)
spike2 = exponential(λ2) + spike1
spikes = RandArray([spike1, spike2])
times = [0.4, 1.4]

prob(is_tagged, spikes == times)

using Distributinos

prob_tagged = 0.2
is_tagged = rand(Bernoulli(prob_tagged))
λ = 0.5

spike_train  = Array(Float64, 100)
spike_train[1] = rand(Exponential(λ))

cell_latency = rand(Uniform(0, 5))

light_onset = 3.0
shining_done = false

for i = 2:100
  new_spike = rand(Exponential(λ)) + spike_train[i-1]
  if bool(is_tagged) && (new_spike > light_onset) && !shining_done
    @show is_spike = rand(Bernoulli(0.5))
    if bool(is_spike)
      spike_time = rand(Beta(2.0, 5.0))/2 + cell_latency
      spike_train[i] = spike_time
    else
      spike_train[i] = new_spike
    end
    shining_done = true
  else
    spike_train[i] = new_spike
  end
end
