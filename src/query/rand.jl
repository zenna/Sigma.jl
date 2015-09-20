## Design Decisions
#
# - should we have extra code for where hte number of smaples is 1 or just have
# generic routines which return first element of an array.
#
# - Second majo design question is who what kind of random variable to pass to the solver
# initially we tried to make the preimage smaplers agnostic to what type of random variable
# it was passed.  The randvar need only implement call(X, A).  However
# -- If the algorith is parallelised, it may need generate the C typed rand Varvar
# -- sol 1. Make these preimage samplers expect the RandVar type and they can do their own conversion
# -- sol 2. Have some kind of buffer between the different cases

# How might that work, well we say

## Unconditional Sampling
## ======================
rand{T}(X::ExecutableRandVar{T}) = call(X,LazyRandomVector(Float64))

"Generate `n` unconditioned random samples from distribution of X"
rand{T}(X::ExecutableRandVar{T}, n::Integer) =
  T[call(X, LazyRandomVector(Float64)) for i = 1:n]

rand{T}(X::SymbolicRandVar{T}, n::Integer) =
  rand(convert(ExecutableRandVar{T},X),n)

##  Rand Arrays
"Generate `n` unconditioned random array samples from distribution of X"
rand{T}(X::ExecutableRandArray{T}, n::Integer) =
  Array{T}[call(X, LazyRandomVector(Float64)) for i = 1:n]

"Generate `n` unconditioned random array samples from distribution of X"
rand{T,N}(Xs::RandArray{T,N}, n::Integer) = rand(convert(ExecutableRandArray{T},Xs),n)

## RandVar{Bool} Preimage Samples
## ==============================

# Note args named x_sampler sample *from* x, e.g.
# partition_sampler samples set from partition (not a partition itself)

"`n` abstract samples from preimage: Y^-1({true})"
function abstract_sample_partition(
    Y::SymbolicRandVar{Bool},
    n::Integer;
    partition_alg::Type{BFSPartition} = BFSPartition,
    args...)

  partition = pre_partition(Y, partition_alg; args...)
  rand(preiamge, n)
end

"`n` point Sample from preimage: Y^-1({true})"
function point_sample_partition{T<:PartitionAlgorithm}(
    Y::SymbolicRandVar{Bool},
    n::Integer;
    partition_alg::Type{T} = BFSPartition,
    partition_sampler::Function = point_sample,
    args...)
  # FIXME: Float64 too specific
  p = pre_partition(Y, partition_alg; args...)
  s_p = SampleablePartition(p)
  partition_sampler(s_p, n)
end

## Markokv Chain Conditional Sampling
## ==================================
"`n` approximate point sample from preimage: Y^-1({true})"
function point_sample_mc{T<:MCMCAlgorithm}(
    Y::SymbolicRandVar{Bool},
    n::Integer;
    ChainAlg::Type{T} = AMS,    # Generate Markov Chain of samples
    chain_sampler::Function = point_sample, # Sample from Markov Chain
    args...)

  # FIXME: Float64 too specific
  chain = pre_mc(Y, n, ChainAlg; args...)
  chain_sampler(chain)
end

## Samples from X given Y
## ======================

# FIXME, this is not the best way to do it.  This method, finds the preiamge samples
# Then just runs them using interva arithmetic.  In order to do this properly you
# need to pave both ways

"`n` conditional samples from `X` given `Y` is true"
function rand{T}(
    X::SymbolicRandVar{T},
    Y::SymbolicRandVar{Bool},
    n::Integer;
    preimage_sampler::Function = point_sample_mc,
    args...)

  executable_X = convert_psuedo(ExecutableRandVar{T}, X)
  preimage_samples = preimage_sampler(Y, n; args...)
  T[call(executable_X, sample) for sample in preimage_samples]
end

"When `X` is a rand var"
function rand{T}(
    X::RandArray{T},
    Y::SymbolicRandVar{Bool},
    n::Integer;
    preimage_sampler::Function = point_sample_mc,
    args...)

  executable_X = convert_psuedo(ExecutableRandArray{T}, X)
  preimage_samples = preimage_sampler(Y, n; args...)
  Array{T}[call(executable_X, sample) for sample in preimage_samples]
end

"Sample from a tuple of values `(X_1, X_2, ..., X_m) conditioned on `Y`"
function rand(
    X::Tuple,
    Y::SymbolicRandVar{Bool},
    n::Integer;
    preimage_sampler::Function = point_sample_mc,
    args...)

  preimage_samples = preimage_sampler(Y, n; args...)

  # There are two natural ways to return the tuples
  # 1. tuple of m (num in tuple) vectors, each n samples long
  # 2. vector of `n` tuples of length `m` <-- we do this oen

  # types = map(x->Vector{rangetype(x)}, X)
  samples = Any[]
  for x in X
    RT = rangetype(x)
    executable_X = executionalize(x)
    xsamples = RT[call(executable_X, sample) for sample in preimage_samples]
    push!(samples, xsamples)
  end
  tuple(samples...)
end

## One Sample
## ==========

"Generate a sample from a rand array `Xs` conditioned on `Y`"
rand(Xs::RandArray, Y::SymbolicRandVar{Bool}; args...) =  rand(Xs,Y,1;args...)[1]

"Generate a sample from a rand array `Xs` conditioned on `Y`"
rand(Xs::Ex, Y::SymbolicRandVar{Bool}; args...) =  rand(Xs,Y,1;args...)[1]

"Generate a sample from a randvar `X` conditioned on `Y`"
rand(X::SymbolicRandVar, Y::SymbolicRandVar{Bool}; args...) = rand(X,Y,1; args...)[1]

"Generate an unconditioned random sample from X"
rand{T}(X::SymbolicRandVar{T}) = rand(X,1)[1]
