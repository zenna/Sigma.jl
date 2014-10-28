import Base: length, dot, sum

type PureRandArray{T,N} <: RandVar{Array{T,N}}
  array::Array{RandVarSymbolic{T},N}
end

typealias PureRandVector{T} PureRandArray{T,1}
typealias PureRandMatrix{T} PureRandArray{T,2}

## Constructor
PureRandArray(T::DataType, nrows::Int64) =
  PureRandArray{T,1}(Array(RandVarSymbolic{T},nrows))
PureRandArray(T::DataType, nrows::Int64, ncols::Int64) =
  PureRandArray{T,2}(Array(RandVarSymbolic{T},nrows,ncols))

rangetype(Xs::PureRandArray) = Array{typeof(Xs).parameters[1]}
call(Xs::PureRandArray, ω) = map(x->call(x,ω),Xs.array)

## Primitive Array Functions
## =========================
# PERF: anon function calls are slow
sum{T}(Xs::PureRandArray{T}, ω) = sum(map(x->call(x,ω), Xs.array))
sum{T}(Xs::PureRandArray{T}) = RandVarSymbolic(T,:(sum($Xs,ω)))
length(Xs::PureRandArray) = RandVarSymbolic(Int64,:(length($Xs.array)))

# PERF: use list comprehensions for speed
rand{T}(Xs::PureRandArray{T}) = map(rand,Xs.array)::Array{T}

## Array Access/Updating
## =====================
getindex{T}(X::PureRandVector{T}, i::Int64) =
  RandVarSymbolic(T,:(pipeomega($X.array[$i],ω)))
getindex{T}(X::PureRandArray{T}, i::Int64, j::Int64) =
  RandVarSymbolic(T,:(pipeomega($X.array[$i,$j],ω)))

setindex!{T}(X::PureRandVector,v::T,i::Int64) = X.array[i] = v
setindex!{T}(X::PureRandArray,v::T,i::Int64,j::Int64) = X.array[i,j] = v

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
    function ($op){T<:ConcreteReal,D}(X::PureRandArray{T,D}, Y::PureRandArray{T,D})
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
