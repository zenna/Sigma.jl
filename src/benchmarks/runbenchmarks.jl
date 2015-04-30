using Sigma
using DynamicAnalysis

benchmarks = ["simplex"]

println("Running Benchmarks:")

for t in benchmarks
    benchmark_fn = joinpath(t,"$t.jl")
    println(" * $benchmark_fn")
    include(benchmark_fn)
end
