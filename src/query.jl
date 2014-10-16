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
rand(X::RandomVariable) = X(SampleOmega())

type ConditionalRandomVariable
  over_pre_cond
  c::Categorical
  X::RandomVariable
  Y::RandomVariable
end

function rand(C::ConditionalRandomVariable; maxtries = Inf, countrejected = false)
  nrejected = 0
  ntried = 0
  while true
    omega = C.over_pre_cond[rand(C.c)]
    sample = rand(omega)
    if call!(C.Y,sample)
      return countrejected ? (call!(C.X,sample), nrejected) : call!(C.X,sample)
    else
      nrejected = nrejected + 1
    end
    ntried += 1
    if ntried == maxtries
      return nothing
    end
  end
end

function cond(X::RandomVariable, Y::RandomVariable; max_depth = 10)
  # Find preimage and measure each box in disjunction
  tree = pre_deepening(Y, T, Omega(), max_depth = max_depth)
  over_pre_cond = mixedsat_tree_data(tree)
  measures::Vector{Float64} = measure(over_pre_cond)
  pnormalize!(measures)
  c = Categorical(measures, Distributions.NoArgCheck())
  ConditionalRandomVariable(over_pre_cond,c,X,Y)
end

# Conditional probability found using samples
function prob_sampled(X::RandomVariable; nsamples = 1000)
  samples = [rand(X) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end

function cond_prob_sampled(X::RandomVariable, Y::RandomVariable; nsamples = 1000)
  C = cond(X,Y)
  samples = [rand(C) for i=1:nsamples]
  length(filter(x->x,samples))/length(samples)
end

# FIXME: DEPRECATE
function cond_sample(X::RandomVariable, Y::RandomVariable; max_depth = 10)
  # Find preimage and measure each box in disjunction
  tree = pre_deepening(Y, T, Omega(), max_depth = max_depth)
  over_pre_cond = mixedsat_tree_data(tree)
  measures::Vector{Float64} = measure(over_pre_cond)
  pnormalize!(measures)
  c = Categorical(measures, Distributions.NoArgCheck())

  # Return a function which can be plot_sample_cond_density
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
