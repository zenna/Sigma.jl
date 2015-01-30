using Sigma
using DataFrames

## Smokers and Friends: Undirected Graph
## =====================================
edges = readtable("problem-7-friends.csv")
edges = edges[:,2:end] # remove "Node" column
nsmokers = length(edges)
issmoker = RandVarSymbolic{Bool}[flip(.2) for i = 1:length(edges)]
issmoker_randvar = PureRandArray(issmoker)

# noisyeq(a,b) = flip(ifelse(a == b, 1.0, 0.2))
noisyeq(a,b) = (a == b) | flip(.75)
condition = RandVarSymbolic{Bool}[]
for i = 1:length(edges), j = 1:length(edges)
  if edges[i,j] == 1
    push!(condition, noisyeq(issmoker[i],issmoker[j]))
  end
end
mrv_condition = (&)(condition...)

@show cond_sample_mh(issmoker_randvar,mrv_condition,10)

## Benchmarks
# Query1: Compute the marginal probability of smoking for each of the
# unobserved nodes given the six observed nodes:
observed_smokers = [1,8,9,15]
observed_nonsmokers = [4,6]
smoker_obs = (&)(vcat([issmoker[i] for i in observed_smokers],[issmoker[i] for i in observed_nonsmokers])...)

fraction_true(x::Vector{Bool}) = count(identity,x)/length(x)

marginals = Dict{Int,Float64}[]
for i = 1:nsmokers
  if (i ∉ observed_smokers) && (i ∉ observed_nonsmokers)
    marginals[i] = cond_prob_mh(issmoker[i], smoker_obs & mrv_condition,10)
  end
end
@show marginals

