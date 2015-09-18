"Uniform sample of subset of preimage of `Y` under `f` unioned with `X`."
function pre_mc{T}(
    Y::SymbolicRandVar{Bool},
    niters::Integer,
    ::Type{T};
    RandVarType::Type = default_randvar(),
    args...)

  init_box = unit_box(LazyBox{Float64}, dims(Y))
  Y_conv = convert(RandVarType, Y)
  pre_mc(Y_conv, init_box, niters, T; args...)
end
