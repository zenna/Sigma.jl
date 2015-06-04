## Parameter Estimation
## ====================

using Sigma


# Parameter to estimate
μ = exponential(1.5)
s = exponential(0.5)
params = PureRandArray(Any[μ,μ])

npoints = 10
# Generate random data for testing
data = [rand()*20 for i = 1:npoints]
sample_rvs = PureRandArray([logistic(μ,μ) for i = 1:npoints])

# Draw 10 Samples from the prior distribution conditioned on the data
@show samples = rand(params,(μ ∈ (1,4)) & (s ∈ (1,4)),100,Sigma.pre_tlmh, Sigma.DRealSolver)
