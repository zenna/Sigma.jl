
## KL-Distribution Test
## ====================
holesizes = logspace(-1,-10,3)
problems = [Simplex(8,        #ndims
                    [:sample_distribution,:accumulative_KL, :total_time,],
                    5,        #nsamples
                    0.01,
                    mvuniform(-2,2,8))]    #holesize

mh_captures = [:samples]
all_splits = [rand_partial_split]

algorithms = [SigmaSMT(mh_captures, randvartype, sampler, nprocs, split)
  for nprocs = [1],
      randvartype = [DRealRandVar],
      split = all_splits,
      sampler = [Sigma.point_sample_mc]][:]

function kl()
  record(algorithms, problems;
         runname = "kl",
         prefix=benchdir,
         exceptions=false)
end

kl()

## Analysis
## This needs a rethink
# How do I want to use this in the end
# a = [run(analysis) or analysis in all_analyses]
# # layer...
typealias DiscreteDistribution Dict{Int, Float64}
#
"returns an output analysis of type O"
abstract Analysis{O}

"Data of relational data X vs Y"
immutable XY{X,Y}
  xdata::Vector{X}
  ydata::Vector{Y}
  xlabel::String
  ylabel::String
end

"""A KL Analysis computes the KL Divergence.
Takes in samples over time and produces output of KL vs time"""
immutable KLAnalysis <: Analysis{XY{Float64, Int}}
  f::XY{Float64, Int}
end

function KLAnalysis(allsamples::Vector{Float64}, truth::DiscreteDistribution)
  for i = 1:length(allsamples)
    samples = allsamples[1:i]
    v = vertex_distribution(samples,ndims,0.01)
    truth = groundtruth(ndims)
    push!(kls,KLsafe(truth,v))
  end
  kls
  XY{Float64,Int64}(samples, )
end

run(x::KLAnalysis) = x.XY


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
