## (Conditional) Probability Queries
## =================================
@doc "Lower and upper bounds for marginal probability that Y is true" ->
function prob(Y::RandVar{Bool};
              partition_alg::Type{BFSPartition} = BFSPartition,
              args...)
  init_box = unit_box(LazyBox{Float64}, dims(Y))
  partition = pre_partition(Y, init_box, partition_alg; args...)
  measure(partition)
end