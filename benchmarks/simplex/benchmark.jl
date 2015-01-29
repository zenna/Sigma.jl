## Simplex Benchmark
## ================
# This benchmark samples from a small region around corners of a n-dimensional
# Simplex. If the regions are of equal size then we should expect an equal
# number of samples in each region.

using Window
using Sigma
using DataStructures

# The vertex coordinates for an ndim simplex
# From http://people.sc.fsu.edu/~jburkardt/m_src/simplex_coordinates/
function simplex_coordinates(n::Int)
  x = zeros(Float64, n, n+1)
  for i = 1 : n
    x[i,i] = sqrt ( 1.0 - sum ( x[1:i-1,i].^2 ) );
    for j = i+1: n+1
      b = (-1.0/n - (x[1:i-1,i]' * x[1:i-1,j])) / x[i,i]
      x[i,j] = b[1]
    end
  end
  return x
end

# Is point p in box with center region and halfwidth halfwidth
function point_near_region(p, region, halfwidth)
  conds = Array(Any,length(p))
  for i = 1:length(p)
    conds[i] = (p[i] >= region[i] - halfwidth) & (p[i] <= region[i] + halfwidth)
  end
  (&)(conds...)
end

# Constrain a point to be within a region around the vertices of a simplex
function simplex(n::Int)
  box = mvuniform(-2,2,n)
  vertexcoords = simplex_coordinates(n)
  conds = RandVar{Bool}[]
  for i = 1:n+1
    push!(conds,point_near_region(box,vertexcoords[:,i],0.1))
  end
  box,(|)(conds...)
end

# From a set of samples compute discrete distribution over the vertices
function vertex_distribution(samples,n)
  vertexcoords = simplex_coordinates(n)
  counts =  DefaultDict(Int, Int, 0)
  for sample in samples
    for i = 1:n+1
      if point_near_region(sample,vertexcoords[:,i], 0.1)
        counts[i] += 1
        break
      end
    end
  end
  counts
end

## Algorithms
## ==========
immutable SimplexBenchmark <: Benchmark
  ndims::Int
  capture::Vector{Symbol}
end

function benchmark(a::SigmaAI, b::SimplexBenchmark)
  global benchmarks
  captures::Vector{Symbol} = vcat(a.capture,b.capture)
  Window.register_benchmarks!(captures)

  groundtruth = [i => 1/(b.ndims+1) for i = 1:(b.ndims+1)]
  model, condition = simplex(b.ndims)
  samples = a.sampler(model,condition, 1000)

  window(:accumulative_KL,accumulative_KL(samples, b.ndims, groundtruth))
    @show vertex_distribution(samples,b.ndims)
  Window.disable_benchmarks!(captures)
  b = benchmarks
  Window.clear_benchmarks!()
  b
end

B = simplex(4)

# smtdistributions!()

## Do Benchmarking
## ==============
# using Gadfly
# disable_all_filters!()
# test_sigma1 = SigmaAI([],rand,1,sqr)
# test_sigma2 = SigmaAI([],cond_sample_mh,1,sqr)
# test_sigma3 = SigmaAI([],Sigma.cond_sample_tlmh,1,sqr)

# test_benchmark = SimplexBenchmark(20,[:sample_distribution, :accumulative_KL])
# # p1  = benchmark(test_sigma1, test_benchmark)
# # p2  = benchmark(test_sigma2, test_benchmark)
# p3  = benchmark(test_sigma3, test_benchmark)
# plot(#layer(y = p1[:accumulative_KL][1], x = 1:1000, Geom.line),
#      layer(y = p3[:accumulative_KL][1], x = 1:1000, Geom.line))
