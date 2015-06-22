import Base: quantile, convert
import Distributions.pnormalize!

abstract InferenceAlgorithm
abstract SamplingAlgorithm <: InferenceAlgorithm
abstract MCMCAlgorithm <: SamplingAlgorithm

## Types of algorithm
# - Preimage Partition: pre_bfs
# - Exact Preimage Sample: ___
# - Approximate Preimage Sample: pre_tlmh
# - Exact Conditional Abstract Sample: __
# - Approximate Conditional Abstract Sample: ___
# - Exact Conditional Point Sample
# - Approximate Conditional Point Sample 

for finame in ["bounds.jl",
               "rand.jl",
               "model.jl"]
    include(joinpath("query", finame))
end
