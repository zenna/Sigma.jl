module SigmaBenchmarking

using Sigma
using Lens
using Compat

# Split Functions
import Sigma: weighted_mid_split, rand_partial_split,
              weighted_partial_split
# Solvers
import Sigma: Solver, DRealSolver, DRealSolverBinary, SigmaSolver

using DynamicAnalysis
import DynamicAnalysis: benchmark

# using DataFrames
# using Gadfly

benchdir = pwd()

include("algorithms.jl")
include("church.jl")

benchmarks = ["simplex"]

println("Running Benchmarks:")

for t in benchmarks
  benchmark_fn = joinpath(t,"$t.jl")
  println(" * $benchmark_fn")
  include(benchmark_fn)
end

end