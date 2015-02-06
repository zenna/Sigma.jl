## Dimension Test
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
                                        :total_time,],1,0.1)
                   for i = 2:10:62]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_partial_split, rand_partial_split]

# SMT algorithms
SMTAlgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [2],
      solver = [z3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIAlgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
  for nprocs = [2],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

dimbenchmarks = SplitBenchmarks
dimalgorithms = vcat(AIAlgorithms,SMTAlgorithms)


runbenchmarks(AIAlgorithms,dimbenchmarks;runname = "dimensions")

# using Gadfly

# function extractdata(data)
  xs = Int64[]
  ys = Float64[]
  for (key,value) in data
    if isa(key[1],Sigma.SigmaAI) & (key[1].split == Sigma.rand_partial_split) & !(isa(value,Exception))
      push!(xs,key[2].ndims)
      push!(ys,value[:total_time][1])
    end
  end
# end

# # Rand split SMT
# plot(x = [6,20,16,30,26,14,12,10,28,18,8,4,2,22,24],
#      y = [13.011885005,256.489656571,127.71078451,752.123698964,496.484901629,98.558202318,71.843140398,41.183985416,664.071571283,180.454738625,25.195943663,4.50651888,1.256410641,294.636191188,384.058506053], Geom.line)

# # SMt Weighted Partial Split
# plot(y = [19.871517743,33.501616323,11.487123464,405.106928473,332.24927191,3.450550429,88.607793944,1.162512879,277.990990788,203.635011443,243.855978834,170.414683246,42.959482655,66.204113471,7.14161407],
#      x = [10,12,8,30,28,4,18,2,26,22,24,20,14,16,6], Geom.line)
# # AI weighted split
# plot(x = [24,2,16,6,18,26,10,28,8,12,4,30,14,20,22], y = [17.65186648,1.243326702,4.666299409,0.319582324,6.233854256,22.748533103,1.007933536,29.050127148,0.609038764,1.814690567,0.164571561,50.687513444,2.983420971,9.907827246,14.34077483], Geom.line)

# # AI rand partial split
# plot(y = [44.101825938,6.654024226,33.385988671,23.40312112,4.185090303,3.039394481,13.501202084,9.471848048,0.820727576,19.288896369,55.487252981,0.175479435,0.365668565,0.060729855,1.425457634],
#      x = [28,16,26,24,14,12,20,18,8,22,30,4,6,2,10], Geom.line)
