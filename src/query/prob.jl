## (Conditional) Probability Queries
## =================================
function prob(Y::SymbolicRandVar{Bool};
              partition_alg::Type{BFSPartition} = BFSPartition,
              args...)
  # init_box = unit_box(LazyBox{Float64}, dims(Y))
  partition = pre_partition(Y, partition_alg; args...)
  res = measure(partition)
  AbstractDomains.Interval(max(0.0, res.l), min(1.0, res.u))
end

function prob_conj(XY::SymbolicRandVar{Bool},
              Y::RandVar{Bool};
              partition_alg::Type{BFSPartition} = BFSPartition,
              args...)
  # init_box = unit_box(LazyBox{Float64}, dims(Y))
  Y_partition = pre_partition(Y, partition_alg; args...)
  Y_measure = measure(Y_partition)
  isequal(Y_measure, zero(Y_measure)) && error("Cannot condition on unsatisfiable events")

  XY_partition = pre_partition(XY, partition_alg; args...)
  res = measure(XY_partition) / Y_measure
  AbstractDomains.Interval(max(0.0, res.l), min(1.0, res.u))
end

# "Lower and upper bounds for marginal probability that 'Y' is true"
# function prob(Y::SymbolicRandVar{Bool}; RandVarType = default_randvar(), args...)
#   executable_Y = convert(RandVarType{Bool}, Y)
#   prob(executable_Y; args...)
# end

"Lower/upper bounds for conditional probability that `X` is true given `Y` is true"
function prob(X::SymbolicRandVar{Bool},
              Y::SymbolicRandVar{Bool};
              args...)
  # executable_Y = convert(RandVarType{Bool}, Y)
  # # We do & here because after conversion & may not be defined on
  # # compiled RandVar types
  # executable_XY = convert(RandVarType{Bool}, X & Y)
  prob_conj(X & Y, Y; args...)
end
