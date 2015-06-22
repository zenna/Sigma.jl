@doc "Random Variables are functions from the sample space to some other space" ->
abstract RandVar{T}

@doc "A symbolic *canonical* representation of a random variable" ->
abstract SymbolicRandVar{T} <: RandVar{T}

@doc "Can be excuted as a normal julia function" ->
type ExecutableRandVar{T} <: RandVar{T}
  func::Function
  dims::Set{Int}
end

@doc """An array of random variables (and also a random variable itself)
  `T` is the range type of elements (e.g for multivariate normal, T = Float64)
  `N` is the dimensionality of array""" ->
type RandArray{T,N} <: DenseArray{RandVar{T},N}
  array::Array{RandVar{T},N}
end

@doc "The type of the range of a random variable" ->
rangetype{T}(X::RandVar{T}) = T

@doc "Number of dimensions of a random variable" ->
ndims(X::RandVar) = length(dims(X))

## Aliases
typealias Lift{T} Union(T,SymbolicRandVar{T})
typealias AllRandVars Union(RandVar, RandArray)

for finame in ["symbolic.jl",
               "executable.jl",
               "randarray.jl"]
    include(joinpath("randvar", finame))
end