import Base: length, dot

type MixedRandomArray{E} <: RandomVariable
  array::Array{Union(E,RandomVariable{E})}
end

type PureRandomArray{E} <: RandomVariable
  array::Array{RandomVariable{E}}
end

FixedLengthRandomArray = Union(MixedRandomArray,PureRandomArray)

## Primitive Array Functions
## =========================

length(X::FixedLengthRandomArray) = RandomVariable(Int64,:(ω->length($X.array)))

# FIXME: X should be a subtype of the union FixedLengthRandomArray
sum{T}(X::RandomArray{T}) = RandomVariable(T,:(ω->sum($X.array)))

## Array Access/Updating
## =====================
getindex{T}(X::MixedRandomArray{T}, i::Int64, j::Int64) =
  RandomVariable(T,:(ω -> pipeomega(X.array[i,j],ω)))
getindex{T}(X::PureRandomArray{T}, i::Int64, j::Int64) =
  RandomVariable(T,:(ω -> X.array[i,j],ω))

setindex{T}(X::RandomArray,v::T,i::Integer,j::Integer) = X.array[i,j] = v

## Complex Array Functions
## =======================

function dot(A::RandomArray,B::RandomArray)
  @assert length(A.array) == length(B.array)
  array = [A.array[i] * B.array[i] for i = 1:length(A.array)]
  sum(array)::RandomVariableSymbolic{Float64}
end

## Generators
## ==========

# Expets a unary primtive constructor which creates random variables, e.g.: i->uniform(i,0.,1.)
function iid(T::DataType, constructor::Function, x::Integer, y::Integer, offset::Integer = 0)
  array::Array{RandomVariable{T}} = [constructor(i+(j-1)*(y-1)) for i = 1:x, j = 1:y]
  PureRandomArray{T}(array)
end
