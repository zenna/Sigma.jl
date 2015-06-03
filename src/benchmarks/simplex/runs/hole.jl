## Simple Hole Test
## ================
import Sigma: Simplex, weighted_mid_split, rand_partial_split,
              weighted_partial_split
import Sigma: dreal, z3, dreal3
import Sigma: SigmaSMT, SigmaIBEX
import Sigma: cond_sample_tlmh
import Sigma: runbenchmarks, benchdir

# Vary the size of the holes around the vertices of the simples
holesizes = logspace(-1,-10,10)
problems = [Simplex(3,[:total_time,],100,h)
              for h = holesizes]

mh_captures = [:start_loop, :refinement_depth, :samples]
all_splits = [weighted_partial_split, rand_partial_split]

SMTalgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1],
      solver = [dreal3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIalgorithms = [SigmaIBEX(mh_captures, sampler, nprocs, split)
  for nprocs = [1],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

for i = 1:10
runbenchmarks(vcat(AIalgorithms),problems;
              runname = "holesize",prefix=benchdir,savedb=true)
end
