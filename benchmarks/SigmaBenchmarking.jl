module SigmaBenchmarking

using Sigma
using Lens
using Compat
# using DataFrames
# using Gadfly

# Split Functions
import Sigma: weighted_mid_split, rand_partial_split,
              weighted_partial_split
# Solvers
import Sigma: Solver, DRealSolver, DRealSolverBinary, SigmaSolver

using DynamicAnalysis
import DynamicAnalysis: benchmark


benchdir = pwd()

include("algorithms.jl")
include("church.jl")

benchmarks = ["simplex"
              "polyfrompixels"]

println("Running Benchmarks:")

for t in benchmarks
  benchmark_fn = joinpath(t,"$t.jl")
  println(" * $benchmark_fn")
  include(benchmark_fn)
end

"""
Evaluate the performance of Sigma on a bench marks.

- each benchmark is contained within its own folder (e.g. ./simplex)
- each folder contains a julia file of the same name (e.g. simplex/simplex.jl)

"""
SigmaBenchmarking

end
