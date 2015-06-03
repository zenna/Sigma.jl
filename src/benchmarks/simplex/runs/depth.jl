## Dimension Test
## ==============
using Sigma
import Sigma: SimplexBenchmark, weighted_mid_split, rand_partial_split,
              weighted_partial_split
import Sigma: dreal, z3, dreal3
import Sigma: SigmaSMT, SigmaIBEX
import Sigma: cond_sample_tlmh
import Sigma: runbenchmarks

SplitBenchmarks = [Simplex(i,[:sample_distribution,
                                        :accumulative_KL,
                                        :total_time,],400,.1)
                   for i = [3,10]]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_partial_split, rand_partial_split]

# SMT algorithms
SMTAlgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1],
      solver = [dreal3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIAlgorithms = [SigmaIBEX(mh_captures, sampler, nprocs, split)
  for nprocs = [1],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

dimbenchmarks = SplitBenchmarks
dimalgorithms = vcat(AIAlgorithms,SMTAlgorithms)

runbenchmarks(AIAlgorithms,dimbenchmarks;runname = "depth")

# # function extractdata(data)
#     xs = Int64[]
#     ys = Vector[]
#     for (key,value) in data
#       if (key[1].split == Sigma.rand_partial_split) & !(isa(value,Exception))
#         push!(xs,key[2].ndims)
#         push!(ys,value[:refinement_depth])
#       end
#     end