## Distribution Test
## =================
holesizes = logspace(-1,-10,3)
problems = [Simplex(8,[:sample_distribution, :accumulative_KL,
                       :total_time,],1000,0.01)]

mh_captures = [:samples]
all_splits = [rand_partial_split]

SMTalgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1],
      solver = [z3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIalgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
  for nprocs = [1],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

function kl()
  record(AIalgorithms,problems;
         runname = "kl",prefix=benchdir,savedb=true,exceptions=false)
end

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
