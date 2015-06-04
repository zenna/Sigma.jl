module SigmaBenchmarking

using Sigma
using Compat

import Sigma: Simplex, weighted_mid_split, rand_partial_split,
              weighted_partial_split
import Sigma: cond_sample_tlmh

using DynamicAnalysis
import DynamicAnalysis: benchmark

using DataFrames
using Gadfly

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