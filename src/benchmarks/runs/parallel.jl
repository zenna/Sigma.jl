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

# function extractdata()
#   ys = Float64[]
#   xs = Int64[]
#   for (key,value) in data
#     if isa(key[1],Sigma.SigmaAI)
#       push!(xs,key[1].ncores)
#       push!(ys,value[:total_time][1])
#     end
#   end
# end

# #SMT
# plot(x=[18,12,17,37,33,21,35,40,28,6,13,3,31,23,20,11,39,34,29,32,30,15,24,22,26,7,19,16,2,36,14,8,25,38,10,4,27,5,9,1],
#      y= [30.088652276,32.454835351,31.956475104,30.622136539,29.046722726,30.295537073,30.677160721,30.595505191,30.178511233,33.0408161,33.241083416,29.945061056,28.987676502,27.883390746,36.806507415,32.494068589,30.785560356,31.770079567,29.967980785,30.861685656,30.513410012,30.945352803,30.000664329,29.683638232,30.993137568,34.90705489,30.431204351,30.595890113,45.953667995,28.413354981,33.004421108,31.591543316,31.76427943,32.249786349,33.392272495,31.934607426,30.708056486,32.061471006,31.45082343,48.719286872], Geom.line)
# plot(x = [31,9,23,10,17,16,35,5,40,27,18,4,34,32,12,7,2,11,8,1,13,3,33,26,21,28,14,38,22,36,39,25,24,15,30,37,19,20,6,29], y = [0.663763885,0.795551611,0.715931824,0.731583818,0.974614338,0.65141427,0.881060887,0.716975545,0.694817954,0.812678691,0.773986244,0.696794102,0.725649725,0.793091758,0.665638965,0.794086698,1.991063103,0.664803417,0.679153679,4.684491724,0.6393919,1.776576016,0.719184689,0.76449543,0.906088166,0.667785573,0.753942407,0.759590093,0.631475561,0.736668336,0.704332105,0.742905691,0.851447618,0.646210437,0.67289623,0.784782175,0.698064856,0.743893172,0.907585122,0.795386601],Geom.line)
