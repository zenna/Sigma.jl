import Base: length, dot, sum, ndims, endof

type PureRandArray{T,N} <: RandVar{Array{T,N}}
  array::Array{RandVarSymbolic{T},N}
end

typealias PureRandVector{T} PureRandArray{T,1}
typealias PureRandMatrix{T} PureRandArray{T,2}

## Constructors
## ============
PureRandArray{T,N}(xs::Array{RandVarSymbolic{T},N}) = PureRandArray{T,N}(xs)
PureRandArray(T::DataType, nrows::Int64) =
  PureRandArray{T,1}(Array(RandVarSymbolic{T},nrows))
PureRandArray(T::DataType, nrows::Int64, ncols::Int64) =
  PureRandArray{T,2}(Array(RandVarSymbolic{T},nrows,ncols))

## Conversion
## ==========
convert{T,N}(::Type{PureRandArray{T,N}}, A::Array{RandVarSymbolic{T},N}) = PureRandArray{T,N}(A)
convert{T,N}(::Type{PureRandArray}, A::Array{RandVarSymbolic{T},N}) = PureRandArray{T,N}(A)

rangetype(Xs::PureRandArray) = Array{typeof(Xs).parameters[1]}
call{T}(Xs::PureRandArray{T,1}, ω) = [call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::PureRandArray{T,2}, ω) = [call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

## Array Access/Updating
## =====================
getindex(Xs::PureRandVector, i::Int64) = Xs.array[i]
getindex(Xs::PureRandVector, i::Int64, j::Int64) = Xs.array[i,j]

setindex!{T}(X::PureRandVector,v::T,i::Int64) = X.array[i] = v
setindex!{T}(X::PureRandArray,v::T,i::Int64,j::Int64) = X.array[i,j] = v

ndims{T,N}(Xs::PureRandArray{T,N}) = N
size(Xs::PureRandArray, i) = size(Xs.array, i)
size(Xs::PureRandArray) = size(Xs.array)
endof(Xs::PureRandArray) = endof(Xs.array)

getindex(Xs::PureRandMatrix, i::Int64, js::UnitRange{Int64}) = PureRandArray(Xs.array[i,js])
getindex(Xs::PureRandMatrix, is::UnitRange{Int64}, j::Int64) = PureRandArray(Xs.array[is,j])
getindex(Xs::PureRandMatrix, is::UnitRange{Int64}, js::UnitRange{Int64}) = PureRandArray(Xs.array[is,js])
getindex(Xs::PureRandVector, is::UnitRange{Int64}) = PureRandArray(Xs.array[is])

## Primitive Array Functions
## =========================
# PERF: anon function calls are slow
# sum{T}(Xs::PureRandArray{T}, ω) = sum(map(x->call(x,ω), Xs.array))
sum{T}(Xs::PureRandArray{T}, ω) = sum(call(Xs,ω))
#   sum(map(x->call(x,ω), Xs.array))


sum{T}(Xs::PureRandArray{T}) = RandVarSymbolic(T,:(sum($Xs,ω)))
length(Xs::PureRandArray) = RandVarSymbolic(Int64,:(length($Xs.array)))

# PERF: use list comprehensions for speed
rand{T}(Xs::PureRandArray{T}) = map(rand,Xs.array)::Array{T}

## Complex Array Functions
## =======================
function dot(A::PureRandVector,B::PureRandVector)
  @assert length(A.array) == length(B.array)
  array = [A.array[i] * B.array[i] for i = 1:length(A.array)]
  sum(array)::RandVarSymbolic{Float64}
end

## Arithmetic
## ==========

# Here, we extract the arrays of both args and apply op
# An alternative is to have a RandVarSymbolic which
# Only when called with an omega will do the array computations on abstract values
# this may be preferable
for op = (:+, :-, :*, :/, :(==), :!=, :&, :|)
  @eval begin
    function ($op){T,D}(X::PureRandArray{T,D}, Y::PureRandArray{T,D})
      let op = $op
        PureRandArray{T,D}(($op)(X.array,Y.array))
      end
    end

#     ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
#     ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

## Generators
## ==========

# Creates a RandArray where each element is returned by unary constructor
# constructor expects integer arg, should correspond to component of ω, e.g. i->uniform(i,0.,1.)
# i values start at offset + 1
function iid(T::DataType, constructor::Function,
             nrows::Int64, ncols::Int64; offset::Int64 = 0)
  array::Array{RandVarSymbolic{T}} = [constructor(i+(j-1)*(nrows) + offset)
                                      for i = 1:nrows, j = 1:ncols]
  PureRandArray{T,2}(array)
end

## Create an iid vector
function iid(T::DataType, constructor::Function, nrows::Int64; offset::Int64 = 0)
  vector::Vector{RandVarSymbolic{T}} = [constructor(i + offset) for i = 1:nrows]
  PureRandVector{T}(vector)
end
