## Parameter Estimation
## ====================

using Sigma


# Parameter to estimate
μ = exponential(0.5)
s = exponential(0.5)
params = PureRandArray(Any[μ,s])

npoints = 5
# Generate random data for testing
data = [rand()*20 for i = 1:npoints]
sample_rvs = PureRandArray([logistic(μ,s) for i = 1:npoints])

# Draw 10 Samples from the prior distribution conditioned on the data
<<<<<<< HEAD
@show samples = rand(params,(μ ∈ (1,4)) & (s ∈ (1,4)),1000,Sigma.pre_tlmh, Sigma.DRealSolverBinary)
=======
@show samples = rand(params,(μ ∈ (1,4)) & (s ∈ (1,4)),100,Sigma.pre_tlmh, Sigma.DRealSolver)
>>>>>>> 63dfe40891f1cdbcea4660d2b9d52106562fa7b8
