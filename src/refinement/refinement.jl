# Structure:
# Generic algorithms pre_partition, pre_mc for different kinds of queries
# These are implemented by concrete algorithms which specialise on type

"Extracts properties (e.g. samples, probabilities) from random variables"
abstract type InferenceAlgorithm end

"Generate Partitions of Sets"
abstract type PartitionAlgorithm <: InferenceAlgorithm end
abstract type SamplingAlgorithm <: InferenceAlgorithm end
abstract type MCMCAlgorithm <: SamplingAlgorithm end

"A stop function used as dummy stopping criteria in while loops"
neverstop(_...) = true

"is this box small (enough to be accepted)?"
function issmall(box::Boxes, precision::Float64)::Bool
  for dim in dims(box)
    (measure(box[dim]) > precision) && return false
  end
  return true
end

include("partition.jl")
include("chain.jl")
include("mcmc.jl")

# Concrete algorithms
include("ams.jl")
include("bfs.jl")
