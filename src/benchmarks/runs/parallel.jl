## Parallel Test
## ==============
using Sigma
import Sigma: SimplexBenchmark, weighted_mid_split, rand_partial_split,
              weighted_partial_split
import Sigma: dreal, z3, dreal3
import Sigma: SigmaSMT, SigmaAI
import Sigma: cond_sample_tlmh
import Sigma: runbenchmarks


SplitBenchmarks = [SimplexBenchmark(i,[:sample_distribution,
                                        :accumulative_KL,
                                        :total_time,])
                   for i = 5:5]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_partial_split]

# SMT algorithms
SMTAlgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1:40],
      solver = [dreal],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIAlgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
  for nprocs = [1:40],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

dimbenchmarks = SplitBenchmarks
dimalgorithms = vcat(AIAlgorithms,SMTAlgorithms)


runbenchmarks(dimalgorithms,dimbenchmarks)