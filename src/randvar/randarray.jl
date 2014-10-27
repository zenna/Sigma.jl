import Base: length, dot, sum

type PureRandomArray{T} <: RandVar{Array{T}}
  array::Array{RandVarSymbolic{T}}
end

domaintype(Xs::PureRandomArray) = Array{typeof(Xs).parameters[1]}

## Primitive Array Functions
## =========================
# PERF: anon function calls are slow
sum{T}(X::PureRandomArray{T}, ω) = sum(map(x->call(x,ω), X.array))
sum{T}(X::PureRandomArray{T}) = @show RandVarSymbolic(T,:(sum($X,ω)))
length(X::PureRandomArray) = RandVarSymbolic(Int64,:(length($X.array)))

# PERF: use list comprehensions for speed
rand{T}(X::PureRandomArray{T}) = map(rand,X.array)::Array{T}

## Array Access/Updating
## =====================
getindex{T}(X::PureRandomArray{T}, i::Int64, j::Int64) =
  RandVarSymbolic(T,:(pipeomega(X.array[$i,$j],ω)))

setindex{T}(X::PureRandomArray,v::T,i::Integer,j::Integer) = X.array[i,j] = v

## Complex Array Functions
## =======================
function dot(A::PureRandomArray,B::PureRandomArray)
  @assert length(A.array) == length(B.array)
  array = [A.array[i] * B.array[i] for i = 1:length(A.array)]
  sum(array)::RandVarSymbolic{Float64}
end

## Generators
## ==========

# Creates a RandomArray where each element is returned by unary constructor
# constructor expects integer arg, should correspond to component of ω, e.g. i->uniform(i,0.,1.)
# i values start at offset + 1
function iid(T::DataType, constructor::Function,
             nrows::Int64, ncols::Int64, offset::Int64 = 0)
  array::Array{RandVarSymbolic{T}} = [constructor(i+(j-1)*(nrows) + offset)
                                      for i = 1:nrows, j = 1:ncols]
  PureRandomArray{T}(array)
end
