## Run Benchmarks
## =============

# Consider all valid combinations of options and collate resultss

SplitBenchmarks = [SimplexBenchmark(i,[:sample_distribution,
                                        :accumulative_KL,
                                        :total_time,])
                   for i = 2:4]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_mid_split, weighted_partial_split, rand_partial_split]
# SMT algorithms
SMTAlgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
  for nprocs = [1],
      solver = [dreal,dreal_nra,z3],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

AIAlgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
  for nprocs = [1],
      split = all_splits,
      sampler = [cond_sample_tlmh]][:]

allbenchmarks = SplitBenchmarks
allalgorithms = vcat(AIAlgorithms,SMTAlgorithms)

# Run all the benchmarks with all teh algorithms and collect results
function runbenchmarks{B<:Benchmark, A<:Algorithm}(benches::Vector{B},
                                                   algos::Vector{A})
  results = Dict{(Algorithm, Benchmark),Any}()
  runiter = 1; nruns = length(benches) * length(algos)
  nfailures = 0
  for j = 1:length(benches), i = 1:length(algos)
    println("RUNNING $runiter of $nruns, $nfailures so far")
    try
      results[(algos[i],benches[j])] = benchmark(algos[i], benches[j])
    catch er
      nfailures += 1
      @show er
      @show j
      @show length(benches)
      results[(algos[i],benches[j])] = er
    end
    runiter += 1
  end
  println("$nfailures failures")
  results
end
