## Parameter Estimation
## ====================

using Sigma

# Parameter to estimate
μ = exponential(0.5)
s = exponential(0.5)
params = RandArray(Any[μ,s])

npoints = 5
# Generate random data for testing
data = [rand()*20 for i = 1:npoints]
sample_rvs = RandArray([logistic(μ,s) for i = 1:npoints])

# Draw 10 Samples from the prior distribution conditioned on the data
nsamples = 100
@show samples = rand(params,(μ ∈ (1,4)) & (s ∈ (1,4)), nsamples, Sigma.pre_tlmh)
