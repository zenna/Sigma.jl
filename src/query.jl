import Base: quantile, convert
import Distributions.pnormalize!

# =======
# Measure
# REVIEW: Remove move this to where it belongs, BOX, maybe delete it
measure{B<:Box}(bs::Vector{B}) = map(volume,bs)

# =======
# Queries
sum_empty(x) = if isempty(x) 0 else sum(x) end
function prob_deep(rv::RandVar{Bool};  max_depth = 5, box_budget = 300000)
  tree = pre_deepening(rv, T, Omega(), max_depth = max_depth, box_budget = box_budget)
  under_pre, over_pre = sat_tree_data(tree), mixedsat_tree_data(tree)
  sum_empty(measure(under_pre)), sum_empty(measure(over_pre))
end

function cond_prob_deep(rv::RandVar{Bool}, q::RandVar{Bool}; box_budget = 300000, max_depth = 5)
  tree1 = pre_deepening(rv & q, T, Omega(), max_depth = max_depth, box_budget = box_budget)
  under_pre_cond, over_pre_cond = sat_tree_data(tree1), mixedsat_tree_data(tree1)

  tree2 = pre_deepening(q, T, Omega(), max_depth = max_depth, box_budget = box_budget)
  under_pre_query, over_pre_query =  sat_tree_data(tree2), mixedsat_tree_data(tree2)
  println(" under cond: ", sum_empty(measure(under_pre_cond)),
          " under query: ", sum_empty(measure(under_pre_query)),
          " over_pre_cond: ", sum_empty(measure(over_pre_cond)),
          " over_pre_query: ", sum_empty(measure(over_pre_query)))

  (sum_empty(measure(under_pre_cond))) / (sum_empty(measure(under_pre_query))), (sum_empty(measure(over_pre_cond))) / (sum_empty(measure(over_pre_query)))
end

# Convenience Aliases
prob = prob_deep
cond_prob = cond_prob_deep

## ========
## Sampling

function cond(X::RandVar, Y::RandVar{Bool}; max_depth = 10)
  # Find preimage and measure each box in disjunction
  tree = pre_deepening(Y, T, Omega(), max_depth = max_depth)
  Ypre_overapprox = mixedsat_tree_data(tree)
  measures::Vector{Float64} = measure(over_pre_cond)
  pnormalize!(measures)
  c = Categorical(measures, Distributions.NoArgCheck())
  ConditionalRandVar(Ypre_overapprox,c,X,Y)
end

# Conditional probability found using samples
function prob_sampled(X::RandVar; nsamples = 1000)
  samples = [rand(X) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end

function cond_prob_sampled(X::RandVar, Y::RandVar{Bool}; nsamples = 1000)
  C = cond(X,Y)
  samples = [rand(C) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end
