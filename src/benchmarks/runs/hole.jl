## Simple Hole Test
## ================
import Sigma: Simplex, weighted_mid_split, rand_partial_split,
              weighted_partial_split
import Sigma: dreal, z3, dreal3
import Sigma: SigmaSMT, SigmaAI
import Sigma: cond_sample_tlmh
import Sigma: runbenchmarks, benchdir

# Vary the size of the holes around the vertices of the simples
holesizes = logspace(-1,-20,2)
problems = [Simplex(3,[:sample_distribution, :accumulative_KL,
                       :total_time,],5,h)
              for h = holesizes]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_partial_split, rand_partial_split]

SMTalgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1],
      solver = [dreal3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIalgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
  for nprocs = [1,2],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

runbenchmarks(vcat(AIalgorithms),problems;
              runname = "holesize",prefix=benchdir,savedb=true)

# # using Gadfly

# # function extractdata(data)
#   xs = Float64[]
#   ys = Float64[]
#   for (key,value) in data
#     if isa(key[1],Sigma.SigmaSMT) & (key[1].split == Sigma.rand_partial_split) & !(isa(value,Exception))
#       push!(xs,key[2].holesize)
#       push!(ys,value[:total_time][1])
#     end
#   end
# # end
