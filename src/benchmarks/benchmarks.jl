## Benchmarking to analyse performance of algorithms

## Measures
## =======
# KL Divergence is a measure of the information lost when Q is used to approximate P
KL{T}(P::Dict{T, Float64}, Q::Dict{T, Float64}) =
  sum([log(P[i]/Q[i]) * P[i] for i in keys(P)])

function KLsafe{T}(P::Dict{T, Float64}, Q::Dict{T, Float64})
  Qnew::Dict{T,Float64} = [k => haskey(Q,k) ? Q[k] + 1 : 1 for k in keys(P)]
  totalcounts = sum(values(Qnew))
  Qnew = [k => v/totalcounts for (k,v) in Qnew] #renormalise
  KL(P,Qnew)
end

# Get the accumulative KL divergence over samples
function accumulative_KL(samples, n, groundtruth, holesize)
  kls = Array(Float64, length(samples))
  for i = 1:length(samples)
    sample_counts = vertex_distribution(samples[1:i],n, holesize)
    sample_distribution = [j => c/length(samples[1:i]) for (j,c) in sample_counts]
    kls[i] = KLsafe(groundtruth,sample_distribution)
  end
  kls
end

include("solvers.jl")
# include("geometry.jl")
include("vis.jl")
include("simplex/simplex.jl")
# include("motionplanning/motionplanning.jl")
include("mp2d/mp2d.jl")
