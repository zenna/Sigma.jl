## Parameter Estimation
## ====================

using Sigma
using Lens
using Distributions

Sigma.restart_counter!()
dist(A,B; epsilon = 1.0) = (&)([abs(A[i] - B[i]) < epsilon for i = 1:length(A)]...)

function go()
  # Parameter to estimate
  μ = exponential(0.5)
  s = exponential(0.5)

  μ = uniform(0.01, 0.9)
  s = uniform(0.01, 0.9)

  
  params = RandArray(Any[μ,s])

  npoints = 160
  # Generate random data for testing
  data = [rand(logistic(0.89, 0.05)) for i = 1:npoints]
  @show data
  sample_rvs = RandArray(Any[logistic(μ,s) for i = 1:npoints])

  # Draw 10 Samples from the prior distribution conditioned on the data
  nsamples = 100
  samples = rand((params, sample_rvs), dist(data, sample_rvs; epsilon = 0.001), nsamples; precision=0.001, parallel = true, ncores = nprocs() - 1,  RandVarType=Sigma.SymbolicRandVar)
end

resultsgo, statsgo = capture(go, [:distance, :sat_check, :post_loop])

# @show samples = rand(params,(μ ∈ (1,4)) & (s ∈ (1,4)), nsamples; precision=0.001, parallel = true, RandVarType=Sigma.SymbolicRandVar)
data => [1.3958020814146948,-0.7472215440424936,0.6113618461528288,0.5829786038262489,1.173847955789808,1.0163374471762308,1.088401142993605,0.709411309255464,0.6741488295917022,1.568773368861366,0.6256263201346027,0.1382057695875465,-0.08059791738200761,0.18407243401903778,0.3981171521011716,1.3208680894314109,1.5455281874135531,1.1551051322684018,-1.043456210998993,0.8851426050099236]
