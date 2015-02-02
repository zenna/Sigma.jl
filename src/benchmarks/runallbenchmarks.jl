## Run ALL OF THE BENCHMARKS
using Sigma
results = runbenchmarks(allbenchmarks, allalgorithms, newseed = true)
@show results
