## How well can we sample from the tail of a normal distribution
## =============================================================

function longtail(a::Algorithm, b::LongtailBenchmark)
  X = b.X
  quickbench(sample(a,X,X>y,a.nsamples),vcat(a.captures,b.captures))
end

immutable LongtailBenchmark <: Benchmark
  ndims::Int
  threshold::Float64
  capture::Vector{Symbol}
  nsamples::Int
end

