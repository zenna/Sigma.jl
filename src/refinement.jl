# Pre-image Computation:
# ======================

abstract InferenceAlgorithm

abstract PartitionAlgorithm <: InferenceAlgorithm
abstract SamplingAlgorithm <: InferenceAlgorithm
abstract MCMCAlgorithm <: SamplingAlgorithm

"A stop function used as dummy stopping criteria in while loops"
neverstop(_...) = true

"Is this box small (enough to be accepted)"
function issmall(box::Boxes, precision::Float64)
  for dim in dims(box)
    (measure(box[dim]) > precision)&& return false
  end
  return true
end

include("refinement/partition.jl")
include("refinement/chain.jl")
include("refinement/aim.jl")
include("refinement/bfs.jl")

SIGMA_SOLVER_ON && include(joinpath("refinement","aimcxx.jl"))
