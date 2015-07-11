## (Conditional) Probability Queries
## =================================
"Lower and upper bounds for marginal probability that Y is true"
function prob(Y::RandVar{Bool};
              partition_alg::Type{BFSPartition} = BFSPartition,
              args...)
  init_box = unit_box(LazyBox{Float64}, dims(Y))
  partition = pre_partition(Y, init_box, partition_alg; args...)
  measure(partition)
end

function prob(Y::SymbolicRandVar{Bool}; RandVarType = default_randvar(), args...)
  executable_Y = convert(RandVarType{Bool}, Y)
  prob(executable_Y, args...)
end