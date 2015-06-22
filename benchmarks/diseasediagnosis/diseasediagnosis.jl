## Medical Diagnosis Benchmark
## ==========================

using Sigma
using DataFrames
disease_priors = [0.025851035,0.058152077,0.020436158,0.040025596,
                  0.032941836,0.078530717,0.005548213,0.024689777,
                  0.029336553,0.020641227,0.074125078,0.028544798,
                  0.054423213,0.077353640,0.078099579,0.065297382,
                  0.039513058,0.030245903,0.128596589,0.095504584]
diseases = RandArray(map(p->flip(p),disease_priors))

datapath = joinpath(benchdir, "diseasediagnosis","problem-2-edges.csv")
edges = readtable(datapath)
nfindings = size(edges,2)
nfindings = 10
ndiseases = size(edges,1)

findings = RandVar{Bool}[]
for i = 1:nfindings
  ands = RandVar{Bool}[]
  for j = 1:ndiseases
    if edges[j,i] != 0.0
      push!(ands, diseases[j] & flip(edges[j,i]))
    end
  end
  push!(findings, (|)(ands...))
end

findings_randvar = RandArray(findings)

## Benchmarking

samples = cond_sample_mh(diseases,findings_randvar == [randbool() for i = 1:nfindings],10)
@show samples
