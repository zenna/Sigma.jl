## Run Benchmarks
## =============

# Consider all valid combinations of options and collate resultss

# SplitBenchmarks = [SimplexBenchmark(i,[:sample_distribution,
#                                         :accumulative_KL,
#                                         :total_time,])
#                    for i = 2:2:20]

mh_captures = [:start_loop, :refinement_depth]
all_splits = [weighted_mid_split, weighted_partial_split, rand_partial_split]
# # SMT algorithms
# SMTAlgorithms = [SigmaSMT(mh_captures, solver, sampler, nprocs, split)
#   for nprocs = [1],
#       solver = [dreal3,z3,dreal],
#       split = all_splits,
#       sampler = [cond_sample_tlmh]][:]

# AIAlgorithms = [SigmaAI(mh_captures, sampler, nprocs, split)
#   for nprocs = [1],
#       split = all_splits,
#       sampler = [cond_sample_tlmh]][:]

# allbenchmarks = SplitBenchmarks
# allalgorithms = vcat(AIAlgorithms,SMTAlgorithms)

# Run all the benchmarks with all teh algorithms and collect results
function runbenchmarks{A<:Algorithm, B<:Benchmark}(algos::Vector{A},
                                                   benches::Vector{B};
                                                   newseed = false,
                                                   runname::String = "")
  results = Dict{(Algorithm, Benchmark),Any}()
  runiter = 1; nruns = length(benches) * length(algos)
  nfailures = 0

  thisrundir = joinpath(benchdir, "data", "$(runname)-$(string(Dates.now()))")
  mkdir(thisrundir)

  for j = 1:length(benches), i = 1:length(algos)
    println("\nRUNNING $runiter of $nruns, $nfailures so far")
    print("$(algos[i]) \n")
    print("$(benches[j]) \n")
    newseed && srand(345678) # Set Random Seed
    restart_counter!()
    try
      results[(algos[i],benches[j])] = benchmark(algos[i], benches[j])
      dumpbenchmark(thisrundir,results)
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
  dumpbenchmark(thisrundir,results,"all")
  results
end

function dumpbenchmark(thisrundir,x,suffix::String = "")
  fname = "$(string(Dates.now()))-$suffix"
  path = joinpath(thisrundir, fname)
  f = open(path,"w")
  serialize(f,x)
  close(f)
end
