## Unconditional Sampling
## ======================

@doc "Generate an unconditioned random sample from X" ->
rand{T}(X::ExecutableRandVar{T}) = call(X,LazyRandomVector(Float64))

@doc "Generate `n` unconditioned random samples from distribution of X" ->
rand{T}(X::ExecutableRandVar{T}, n::Integer) =
  T[call(X, LazyRandomVector(Float64)) for i = 1:n]

rand{T}(X::SymbolicRandVar{T}, n::Integer) = 
  rand(convert(ExecutableRandVar{T},X),n)

rand{T}(X::SymbolicRandVar{T}) = rand(X,1)[1]

## RandVar{Bool} Preimage Samples
## ==============================
@doc "`n` abstract samples from preimage: Y^-1({true})" ->
function abstract_sample_partition(Y::RandVar{Bool},
                         n::Integer;
                         partition_alg::Type{BFSPartition} = BFSPartition,
                         args...)
  init_box = unit_box(LazyBox{Float64}, dims(Y))
  partition = pre_partition(Y, init_box, partition_alg; args...)
  rand(preiamge, n)
end

@doc "`n` point Sample from preimage: Y^-1({true})" ->
function point_sample_partition(Y::RandVar{Bool},
                      n::Integer;
                      partition_alg::Type{BFSPartition} = BFSPartition,
                      sampler::Function = point_sample,
                      args...)
  init_box = unit_box(LazyBox{Float64}, dims(Y))
  p = pre_partition(Y, init_box, partition_alg; args...)
  s_p = SampleablePartition(p)
  sampler(s_p, n)
end

## Conditional Sampling
## ====================
@doc "`n` conditional samples from `X` given `Y` is true" ->
function cond_sample{T}(X::ExecutableRandVar{T},
                     Y::RandVar{Bool},
                     n::Integer;
                     preimage_sampler::Function = point_sample_mc,
                     args...)
  RT = rangetype(X)
  preimage_samples = preimage_sampler(Y, n; args...)
  RT[call(X, sample) for sample in preimage_samples]
end
 
@doc "`n` abstract Conditional samples from `X` given `Y` is true" ->
function abstract_cond_sample{T}(X::ExecutableRandVar{T},
                     Y::RandVar{Bool},
                     n::Integer;
                     abstract_preimage_sampler::Function = abstract_sample_partition,
                     args...)
  RT = rangetype(X)
  preimage_samples = abstract_sample_partition(Y, n; args...)
  RT[call(X, sample) for sample in preimage_samples]
end

## Markokv Chain Conditional Sampling
## ==================================
@doc "`n` approximate point Sample from preimage: Y^-1({true})" ->
function point_sample_mc(Y::RandVar{Bool},
                      n::Integer;
                      mc_alg::Type{AIM} = AIM,
                      sampler::Function = point_sample,
                      args...)
  init_box = unit_box(LazyBox{Float64}, dims(Y))
  chain = pre_mc(Y, init_box, n, mc_alg; args...)
  sampler(chain)
end

## Convenience
## ===========
function rand{T}(X::SymbolicRandVar{T},
                 Y::SymbolicRandVar{Bool},
                 n::Integer;
                 RandVarType = default_randvar(),
                 args...)
  @show RandVarType
  executable_Y = convert(RandVarType{Bool}, Y)
  executable_X = convert(ExecutableRandVar{T}, X)
  cond_sample(executable_X, executable_Y, n; args...)
end

function rand(X,
              Y::SymbolicRandVar{Bool},
              n::Integer;
              RandVarType = default_randvar(),
              preimage_sampler::Function = point_sample_mc,
              args...)
  @show RandVarType
  executable_Y = convert(RandVarType{Bool}, Y)
  preimage_samples = preimage_sampler(executable_Y, n; args...)
  [call_type(X, sample) for sample in preimage_samples]
end

function rand(X::RandArray,
              Y::SymbolicRandVar{Bool},
              n::Integer;
              RandVarType = default_randvar(),
              preimage_sampler::Function = point_sample_mc,
              args...)
  executable_Y = convert(RandVarType{Bool}, Y)
  preimage_samples = preimage_sampler(executable_Y, n; args...)
  [call(X, sample) for sample in preimage_samples]
end

function rand(X::RandArray,
              Y::SymbolicRandVar{Bool};
              args...)
  rand(X,Y,1;args...)[1]
end

rand(X::SymbolicRandVar, Y::SymbolicRandVar{Bool}; args...) = rand(X,Y,1; args...)[1]

function rand(X::Tuple,
              Y::SymbolicRandVar{Bool},
              n::Integer;
              RandVarType = default_randvar(),
              preimage_sampler::Function = point_sample_mc,
              args...)
  @show typeof(RandVarType)
  executable_Y = convert(RandVarType{Bool}, Y)
  preimage_samples = preimage_sampler(executable_Y, n; args...)

  # types = map(x->Vector{rangetype(x)}, X)
  samples = Any[]
  for x in X
    RT = rangetype(x)
    xsamples = RT[call(x, sample) for sample in preimage_samples]
    push!(samples, xsamples)
  end
  tuple(samples...)
end