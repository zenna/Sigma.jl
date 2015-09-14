"Random Variables are functions from the sample space to some other space"
abstract RandVar{T}

"All RandVars have an id which is used to make them independent"
typealias Id Integer


"A symbolic *canonical* representation of a random variable"
abstract SymbolicRandVar{T} <: RandVar{T}

"Can be excuted as a normal julia function"
type ExecutableRandVar{T} <: RandVar{T}
  func::Function
  dims::Set{Int}
end

"""An array of random variables (and also a random variable itself)
  `T` is the range type of elements (e.g for multivariate normal, T = Float64)
  `N` is the dimensionality of array"""
type RandArray{T,N} <: DenseArray{T,N}
  array::Array{RandVar{T},N}
end

"A matrix of compiled random variables"
type ExecutableRandArray{T, N} <: DenseArray{T,N}
  array::Array{ExecutableRandVar{T},N}
end

"The type of the range of a random variable"
rangetype{T}(X::RandVar{T}) = T

"Number of dimensions of a random variable"
ndims(X::RandVar) = length(dims(X))

"Set Precision - Generic does nothing"
function set_precision!(Y::RandVar, precision::Float64) end

## Aliases
typealias Lift{T} Union(T,SymbolicRandVar{T})
typealias AllRandVars Union(RandVar, RandArray)

include("randvar/symbolic.jl")
include("randvar/elementary.jl")
include("randvar/executable.jl")
include("randvar/randarray.jl")

# Call An Arbitrary Simple Composite type with an ω
# This calling is quite naive, it just calls all the fields of the type
# with ω.  It does not do any recursive lookup
# And the type must be constructable just by using the parameters (default constructor)
# Use call_type instead of call to avoid mass ambiguity
function call_type{T}(X::T, ω::Omega)
  T.abstract && error("Cannot use abstract type as RandVar")
  properties = Any[]
  for fieldname in fieldnames(X)
    field = getfield(X, fieldname)
    if isa(field, AllRandVars)
      push!(properties, call(field, ω))
    else
      push!(properties, field)
    end
  end
  T(properties...)
end
