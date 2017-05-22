## Simplex Benchmark
## =================
# This benchmark samples from a small region around corners of a n-dimensional
# Simplex. If the regions are of equal size then we should expect an equal
# number of samples in each region.

"""The vertex coordinates for an ndim simplex
From http://people.sc.fsu.edu/~jburkardt/m_src/simplex_coordinates/"""
function simplex_coordinates(n::Int)
  x = zeros(Float64, n, n+1)
  for i = 1 : n
    x[i,i] = sqrt(1.0 - sum(x[1:i-1,i].^2))
    for j = i+1: n+1
      b = (-1.0/n - (x[1:i-1,i]' * x[1:i-1,j])) / x[i,i]
      x[i,j] = b[1]
    end
  end
  return x
end

"Is point p in box with center region and halfwidth halfwidth"
function point_near_region(p, region, halfwidth)
  conds = Array(Any,length(p))
  for i = 1:length(p)
    conds[i] = (p[i] >= region[i] - halfwidth) & (p[i] <= region[i] + halfwidth)
  end
  (&)(conds...)
end

"Constrain a point to be within a region around the vertices of a simplex"
function simplex(n::Int, box::RandArray, holesize)
  vertexcoords = simplex_coordinates(n)
  conds = RandVar{Bool}[]
  for i = 1:n+1
    push!(conds,point_near_region(box,vertexcoords[:,i],holesize))
  end
  box,(|)(conds...)
end

"Ground truth histrogram"
groundtruth(ndims) = Dict(i::Int => (1/(ndims+1))::Float64 for i = 1:(ndims+1))

"Constrain a point to be within a region around the vertices of a simplex"
simplex(n::Int) = simplex(n,mvuniform(-2,2,n))

"From a set of samples compute discrete distribution over the vertices"
function vertex_distribution(samples,n,holesize)
  vertexcoords = simplex_coordinates(n)
  counts =  DefaultDict(Int, Float64, 0.0)
  for sample in samples
    for i = 1:n+1
      if point_near_region(sample,vertexcoords[:,i], holesize)
        counts[i] += 1
        break
      end
    end
  end
  Dict(counts)
end

## Benchmark
## =========
"""Sample from a prior over R^ndim constrained to cubes of size holesize around
vertices of ndim Simplex"""
immutable Simplex <: Problem
  ndims::Int
  capture::Vector{Symbol}
  nsamples::Int
  holesize::Float64
  prior::RandArray
end

function benchmark(a::Algorithm, b::Simplex)
  print("Starting Sampler")
  Sigma.restart_counter!()
  captures::Vector{Symbol} = vcat(a.capture,b.capture)
  groundtruth = Dict(i => 1/(b.ndims+1) for i = 1:(b.ndims+1))
  model, condition = simplex(b.ndims, b.prior, b.holesize)
  @show b.nsamples

  value, results = capture(()->sample(a,model,condition,b.nsamples), captures)
  @show length(value)
  results
end

## Algorithm-dependent implementations of sample
## ============================================
"Sample with SMT based solver"
function sample(a::SigmaSMT, model, condition, nsamples)
  @show model
  @show condition
  @show nsamples
  rand(model, condition, nsamples; preimage_sampler = a.preimage_sampler,
                                   RandVarType = a.randvartype,
                                   cores = a.ncores,
                                   split = a.split)
end

"Sample with rejection sampling"
function sample(a::SigmaRej, X::AllRandVars, Y::RandVar{Bool}, nsamples::Integer)
  box = Sigma.LazyOmega(Float64)
  for dim in dims(Y)
    box[dim]
  end

  Y_func = Sigma.lambda(Y)
  X_func = Sigma.lambda(X)

  samples = []
  ntries = 10000000
  for i = 1:nsamples
    for i = 1:ntries
      ω = rand(box)
      if Y_func(ω)
        println("Got sample with rejection")
        push!(samples,X_func(ω))
        break
      end
    end
  end

  @show length(samples), nsamples
  length(samples) != nsamples && error("Couldn't draw sample")
  return samples
end

"Sample using breadth first search"
function sample(a::SigmaBFS, X::AllRandVars, Y::RandVar{Bool}, nsamples::Integer)
  Sigma.rand_bfs(X,Y,nsamples)
end

## Runs
## ====
include("runs/kl.jl")
# include("runs/dimensions.jl")
