## Distribution Test
## =================
include("../simplex.jl")

holesizes = logspace(-1,-10,3)
problems = [Simplex(4,[:sample_distribution, :accumulative_KL,
                       :total_time,],100,0.01)]

mh_captures = [:samples]
# all_splits = [weighted_partial_split, rand_partial_split]

# SMTalgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
#   for nprocs = [1],
#       solver = [dreal3],
#       split = all_splits,
#       sampler = [cond_sample_tlmh]][:]

IBEXalgorithms = [SigmaIBEX(mh_captures, sampler, nprocs)
  for nprocs = [1],
      sampler = [cond_sample_tlmh]][:]

benchmark(IBEXalgorithms[1],problems[1])

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
