using Sigma
using DataFrames

## Smokers and Friends: Undirected Graph
## =====================================

# noisyeq(a,b) = flip(ifelse(a == b, 1.0, 0.2))
noisyeq(a,b) = (a == b) | flip(.75)

# Given a list of smokers, and an edge graph
# Create the condition that if you have smoke friends you're more
# likely to be a smoker
function smokers_befriend_smokers(issmoker::RandArray, edges)
  condition = RandVar{Bool}[]
  for i = 1:length(edges), j = 1:length(edges)
    if edges[i,j] == 1
      push!(condition, noisyeq(issmoker[i],issmoker[j]))
    end
  end
  (&)(condition...)
end

# Make condition from observations of who is a smoker and who aint
function make_observes(issmoker, observed_smokers, observed_nonsmokers)
  (&)(vcat([issmoker[i] for i in observed_smokers],
           [!issmoker[i] for i in observed_nonsmokers])...)
end


function smokers(issmoker::RandArray{Bool})
  mrv_condition = smokers_befriend_smokers(issmoker)
  observations = make_observes(issmoker, observed_smokers, observed_nonsmokers)

end

function marginals(issmoker, observed_smokers, observed_nonsmokers)
  marginals = Dict{Int,(RandVar, RandVar)}[]
  for i = 1:nsmokers
    if (i ∉ observed_smokers) && (i ∉ observed_nonsmokers)
      marginals[i] = (issmoker[i], smoker_obs & mrv_condition)
    end
  end
  marginals
end

function test_smokers()
  datapath = joinpath(benchdir, "smokers","problem-7-friends.csv")
  edges = readtable(datapath)
  edges = edges[:,2:end] # remove "Node" column
  nsmokers = length(edges)

  # prior prob of being a smoker
  issmoker = RandArray([flip(.2) for i = 1:length(edges)])

  # observations
  observed_smokers = [1,8,9,15]
  observed_nonsmokers = [4,6]

  mrv_condition = smokers_befriend_smokers(issmoker, edges)
  observations = make_observes(issmoker, observed_smokers, observed_nonsmokers)
  issmoker, mrv_condition & observations
#   marginals()
end

issmoker, condition = test_smokers()
# @show condition.smt
# cond_sample_tlmh(issmoker, condition,1;split=rand_partial_split, solver=dreal3)
# ndims(condition)
# @show cond_sample_mh(issmoker_randvar,mrv_condition,10)

# ## Benchmarks
# # Query1: Compute the marginal probability of smoking for each of the
# # unobserved nodes given the six observed nodes:
# smoker_obs = (&)(vcat([issmoker[i] for i in observed_smokers],[issmoker[i] for i in observed_nonsmokers])...)

# fraction_true(x::Vector{Bool}) = count(identity,x)/length(x)

# marginals = Dict{Int,Float64}[]
# for i = 1:nsmokers
#   if (i ∉ observed_smokers) && (i ∉ observed_nonsmokers)
#     marginals[i] = cond_prob_mh(issmoker[i], smoker_obs & mrv_condition,10)
#   end
# end
# @show marginals

