## Simplex Benchmark
## ================
# This benchmark samples from a small region around corners of a n-dimensional
# Simplex. If the regions are of equal size then we should expect an equal
# number of samples in each region.

using Window
using Sigma
using DataStructures

mvuniform(a,b,n,p) = PureRandArray(RandVarSymbolic{Float64}[uniform(a,b) for i = 1:n, j =p])
mvuniform(a,b,n) = PureRandArray(RandVarSymbolic{Float64}[uniform(a,b) for i = 1:n])

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

## Sanity check
# model, condition = simplex(2)
# samples = rand(model,condition, 1000)
# xs = [s[1] for s in samples]
# ys = [s[2] for s in samples]
# plot(x = xs, y = ys)

immutable SimplexBenchmark # <: Benchmark
  ndims::Int
end

# KL Divergence
KL{T}(P::Dict{T, Float64}, Q::Dict{T, Float64}) = sum([log(P[i]/Q[i]) * P[i] for i in keys(P)])

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

function benchmark(b::SimplexBenchmark)
  groundtruth = [i => 1/(b.ndims+1) for i = 1:(b.ndims+1)]
  model, condition = simplex(b.ndims)
  samples = rand(model,condition, 1000)

  sample_counts = vertex_distribution(samples,b.ndims)
  sample_distribution = [i => c/length(samples) for (i,c) in sample_counts]
  @show groundtruth, sample_distribution
  @show KL(groundtruth, sample_distribution)
end

## Do Benchmarking
## ==============
disable_all_filters!()
b = SimplexBenchmark(3)
benchmark(b)


plot(y = [benchmark(SimplexBenchmark(i)) for i = 2:8], x = 2:10, Geom.line)
# Measure KL divergence from true distribution
#