import Base: quantile, convert
import Distributions.pnormalize!

# =======
# Measure
# REVIEW: Remove move this to where it belongs, BOX, maybe delete it
measure{B<:Box}(bs::Vector{B}) = map(volume,bs)

# =======
# Queries

sum_empty(x) = if isempty(x) 0 else sum(x) end
function prob_deep(rv::RandomVariable;  max_depth = 5, box_budget = 300000)
  tree = pre_deepening(rv, T, Omega(), max_depth = max_depth, box_budget = box_budget)
  under_pre, over_pre = sat_tree_data(tree), mixedsat_tree_data(tree)
  sum_empty(measure(under_pre)), sum_empty(measure(over_pre))
end

function cond_prob_deep(rv::RandomVariable, q::RandomVariable; box_budget = 300000, max_depth = 5)
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
function cond_sample(X::RandomVariable, Y::RandomVariable; max_depth = 10)
  tree = pre_deepening(Y, T, Omega(), max_depth = max_depth)
  over_pre_cond = mixedsat_tree_data(tree)
  measures::Vector{Float64} = measure(over_pre_cond)
  pnormalize!(measures)
  println("Sum of normalised weights is", sum(measures))
  c = Categorical(measures, Distributions.NoArgCheck())

  function(num_tries)
    local num_rejected = 0
    for i = 1:num_tries
      omega = over_pre_cond[rand(c)]
      sample = rand(omega)
      if Y(sample)
        return X(sample), num_rejected
      else
        num_rejected = num_rejected + 1
#         println("sample failed, trying again, i = ", i)
      end
    end
  end
end
