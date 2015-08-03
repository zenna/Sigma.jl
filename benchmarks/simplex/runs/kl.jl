## KL-Distribution Test
## ====================
holesizes = logspace(-1,-10,3)
problems = [Simplex(8,        #ndims
                    [:sample_distribution,:accumulative_KL, :total_time,],
                    5,        #nsamples
                    0.01)]    #holesize

mh_captures = [:samples]
all_splits = [rand_partial_split]

algorithms = [SigmaSMT(mh_captures, randvartype, sampler, nprocs, split)
  for nprocs = [1],
      randvartype = [DRealRandVar],
      split = all_splits,
      sampler = [Sigma.point_sample_mc]][:]

function kl()
  record(algorithms,problems;
         runname = "kl",prefix=benchdir,savedb=false,exceptions=false)
end

# The idea is KL runs the actual test, but then there are a bunch of
# analyses that we want to run from that data.

# An analysis is a function from the data to some other set
# Then there is the visualisation of that analysis

# So maybe I should have a type for this in DynamicAnalysis

# I'm not sure what I even want here, what I want is to know how well or poorly
# my algorithms are doing, and whether improvements are actually improvements.
# To know this  I need to be able to see over many changes of algorithm how
# performance changes.  This means I need to decide on the relevant performance
# Metrics.

# For simplex for example there are a bunch of runs that I've set up that measure
# e.g. runtime vs holesize or runtime vs dimensionality or runtime vs distribution
# or a histogram of depths.

# Example Analyses
# - Show me the KL divergences over this set of problems for my algorithm and church
# - Overlay the histograms of depths for AIM using random split vs uniform split for simplex
# - Overlay the histograms of depths for AIM using random split vs uniform split for parameter estimation

# Observations
# An analysis could 'belong' to a single or multiple different problems
# The data may exist for an analysis to compute or it may need to be computed

# Proposal
# Make a type Analysis which simply takes in some data
# computes the output
# Which can be viewed in many forms

"""An abstract analysis takes in Input data of type I,
and returns an output analysis of type O"""
abstract Analysis{I, O}

typealias VertexSamples = Vector{Float64}

"""A KL Analysis computes the KL Divergence.
Takes in samples over time and produces output of KL vs time"""
immutable KLAnalysis <: Analysis{VertexSamples, R}
  f::Function
end

# issues
# - there are many ways teh input could be different
#

KLAnalysis()

## Analyses
## ========

function count(ndims)
  results = DynamicAnalysis.all_records() |> r->DynamicAnalysis.where(r,:runname,j->j=="kl") |> r->DynamicAnalysis.where(r,:problem,j->j.ndims == ndims)
  @show size(results,1)

end

function accumulative_kl(i, ndims)
  records = DynamicAnalysis.all_records() |> r->DynamicAnalysis.where(r,:runname,j->j=="kl") |> r->DynamicAnalysis.where(r,:problem,j->j.ndims == ndims)
  results = records[:results]
  @show length(results)
  allsamples = Lens.get(results[i];lensname=:samples)
  kls = Float64[]
  for i = 1:length(allsamples)
    samples = allsamples[1:i]
    v = vertex_distribution(samples,ndims,0.01)
    truth = groundtruth(ndims)
    push!(kls,KLsafe(truth,v))
  end
  kls
end

function accumulative_mean_kls(dims)
  trials = [accumulative_kl(i, dims) for i = 1:count(dims)]
  mean_kls = Array(Float64, length(trials[1]))
  stds_kls = Float64[]
  for i = 1:length(trials[1])
    total = 0.0
    for j = 1:length(trials)
      total += trials[j][i]
    end
    mean_kls[i] = total/length(trials)
  end
  return mean_kls
end

function plot_kls(dims::Vector{Int})
  dfs = DataFrame[]
  for dim in dims
    akl = accumulative_mean_kls(dim)
    df = DataFrame(x=1:length(akl), y = akl, label = "Dim:$dim")
    push!(dfs,df)
  end
  Gadfly.plot(vcat(dfs...), x="x", y="y", color="label",Gadfly.Geom.line,
     Guide.xlabel("Number of Samples"),
     Guide.ylabel("KL Divergence"))
end


# splitkey = [rand_partial_split => "rand", weighted_mid_split => "mid", weighted_partial_split => "partial"]

# # # Analysis
# # ## KL
# using Lens
# using SQLite
# using Gadfly
# using DataFrames
# q = all_records() |> r->Lens.where(r,"runname",j->j=="kl")
# g = group(q)



# plot_db(y = tree, x = :iterate, groupby=)

# function plot_kl2(groups)
#   dfs = DataFrame[]
#   i = 1
#   for (k,v) in groups
#     results = Result[x[7] for x in v]
#     collated = Lens.collate(results, :samples, :x1)
#     @show length(collated)
#     samples = collated
#     ndims = k[2].ndims
#     holesize = k[2].holesize
#     gt = groundtruth(ndims)
#     akl = accumulative_KL(samples, ndims, gt,holesize)
#     df = DataFrame(x=1:length(akl), y = akl, label = "SMT$i")
#     push!(dfs,df)
#     i += 1
#   end
# #   return  dfs
#   plot(vcat(dfs...), x="x", y="y", color="label",Geom.line,
#        Guide.xlabel("Number of Samples"),
#        Guide.ylabel("KL Divergence"))
# end

# plot_kl2(g)



# draw(PDF("/home/zenna/Dropbox/writing/conferences/icml2015/figures/smt1.pdf",4*1inch,3*1inch), smtplot)
