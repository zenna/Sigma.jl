using Sigma
using Distributions

import Sigma: Exponential, uniform, mvexponential

# Data
λreal = 1.5
n = 10
data = rand(Exponential(λreal),n)

λ = uniform(0,2)
x = mvexponential(λ, n)
observations = x == data
posterior_samples = rand(λ, observations, 10)