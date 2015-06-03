# using Sigma
using Lens
using DynamicAnalysis
include("../algorithms.jl")

## Simplex Benchmark
## =================
# This benchmark samples from a small region around corners of a n-dimensional
# Simplex. If the regions are of equal size then we should expect an equal
# number of samples in each region.

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
function simplex(n::Int, box, holesize)
  vertexcoords = simplex_coordinates(n)
  conds = RandVar{Bool}[]
  for i = 1:n+1
    push!(conds,point_near_region(box,vertexcoords[:,i],holesize))
  end
  box,(|)(conds...)
end

# Ground truth histrogram
groundtruth(ndims) = [i::Int => (1/(ndims+1))::Float64 for i = 1:(ndims+1)]

# Constrain a point to be within a region around the vertices of a simplex
simplex(n::Int) = simplex(n,mvuniform(-2,2,n))

# From a set of samples compute discrete distribution over the vertices
function vertex_distribution(samples,n,holesize)
  vertexcoords = simplex_coordinates(n)
  counts =  DefaultDict(Int, Int, 0)
  for sample in samples
    for i = 1:n+1
      if point_near_region(sample,vertexcoords[:,i], holesize)
        counts[i] += 1
        break
      end
    end
  end
  counts
end

## Benchmark
## =========
immutable Simplex <: Problem
  ndims::Int
  capture::Vector{Symbol}
  nsamples::Int
  holesize::Float64
end

==(a::Simplex, b::Simplex) = equiv(a,b)
hash(s::Simplex, h::Uint) = deephash(s,h)

function simplexbenchmark(a::Algorithm, m::AllRandVars, b::Simplex)
  Sigma.restart_counter!()
  captures::Vector{Symbol} = vcat(a.capture, b.capture)
  groundtruth = [i => 1/(b.ndims+1) for i = 1:(b.ndims+1)]
  model, condition = simplex(b.ndims, m, b.holesize)
  @show b.nsamples

  value, results = capture(()->sample(a,model,condition,b.nsamples), captures; exceptions = false)
  results
end

benchmark(a::SigmaIBEX, b::Simplex) = simplexbenchmark(a, mvuniform(-2,2,b.ndims), b)

sample(a::SigmaSMT, model, condition, nsamples) =
  a.sampler(model,condition, nsamples; ncores = a.ncores, split = a.split, solver = a.solver)

sample(a::SigmaIBEX, model, condition, nsamples) =
   a.sampler(model,condition, nsamples)

## Runs
## ====
