import Base.eltype
import Base.size

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

convert{T,N}(::Type{PureRandArray{T,N}}, A::Array{T,N}) =
  PureRandArray{T,N}(map(a->convert(RandVarSymbolic{T},a),A))
promote_rule{T,N}(::Type{PureRandArray{T,N}}, ::Type{Array{T,N}}) = PureRandArray{T,N}

rangetype(Xs::PureRandArray) = Array{typeof(Xs).parameters[1]}
eltype(Xs::PureRandArray) = rangetype(Xs).parameters[1]
call{T}(Xs::PureRandArray{T,1}, ω) = [call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::PureRandArray{T,2}, ω) = [call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

## Array Access/Updating
## =====================
getindex(Xs::PureRandVector, i::Int64) = Xs.array[i]
getindex(Xs::PureRandMatrix, i::Int64, j::Int64) = Xs.array[i,j]
getindex(Xs::PureRandMatrix, i::Int64) = ((c,r) = divrem(i-1,size(Xs,1)); Xs.array[r+1,c+1])

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

function getindex(Xs::PureRandVector, is::StepRange)
  Ys = PureRandArray(eltype(Xs),length(is))
  j = 1
  for i in is
    Ys[j] = Xs[i]
    j += 1
  end
  Ys
end

## Primitive Array Functions
## =========================
# PERF: anon function calls are slow
# sum{T}(Xs::PureRandArray{T}, ω) = sum(map(x->call(x,ω), Xs.array))
sum{T}(Xs::PureRandArray{T}, ω) = sum(call(Xs,ω))
#   sum(map(x->call(x,ω), Xs.array))


sum{T}(Xs::PureRandArray{T}) = RandVarSymbolic(T,:(sum($Xs,ω)))

# In principle length(Xs) should return a Int-RandVar, but until
# we support indexing on integer random variables it makes things hard
# / inconvenient, so leave this commented
# length(Xs::PureRandArray) = RandVarSymbolic(Int64,:(length($Xs.array)))
length(Xs::PureRandArray) = length(Xs.array)
size(Xs::PureRandArray) = size(Xs.array)
size(Xs::PureRandArray,i::Int) = size(Xs.array, i)

# PERF: use list comprehensions for speed
function rand{T,N}(Xs::PureRandArray{T,N})
  ret::Array{T,N} = call(Xs,SampleOmega())
  return ret
end

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
for op = (:+, :-, :*, :/, :&, :|)
  @eval begin
    function ($op){T,D}(X::PureRandArray{T,D}, Y::PureRandArray{T,D})
      let op = $op
        PureRandArray{T,D}(($op)(X.array,Y.array))
      end
    end

    # Interop with 'normal arrays' promote them to RandArrays
    ($op){T,D}(X::PureRandArray{T,D}, Y::Array{T,D}) = ($op)(promote(X,Y)...)
    ($op){T,D}(X::Array{T,D}, Y::PureRandArray{T,D}) = ($op)(promote(X,Y)...)

    # Point wise arithmetic against rand variable (first arg)
    function ($op){T,D,T2<:Real}(Y::RandVar{T2}, X::PureRandArray{T,D})
      let op = $op
        PureRandArray{T,D}(map(x->($op)(Y,x), X.array))
      end
    end

    # Point wise arithmetic against rand variable (second arg)
    function ($op){T,D,T2<:Real}(X::PureRandArray{T,D}, Y::RandVar{T2})
      let op = $op
        PureRandArray{T,D}(map(x->($op)(x,Y), X.array))
      end
    end

#     ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
#     ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:(==), :!=, :isapprox)
  @eval begin
    function ($op){T,D}(X::PureRandArray{T,D}, Y::PureRandArray{T,D})
      @assert length(X) == length(Y)
      condition = true
      for i = 1:length(X)
        condition = condition & (X.array[i] == Y.array[i])
      end
      condition
    end

    ($op){T,D}(X::PureRandArray{T,D}, Y::Array{T,D}) = ($op)(promote(X,Y)...)
    ($op){T,D}(X::Array{T,D}, Y::PureRandArray{T,D}) = ($op)(promote(X,Y)...)
  end
end

# Unary Functions
for op = (:abs,)
  @eval begin
  function ($op){T,D}(X::PureRandArray{T,D})
    PureRandArray{T,D}(map($op,X.array)) #PERF
  end
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

multivariate_uniform(i::Int, j::Int) = iid(Float64, c->uniform(c,0,1),i,j)
multivariate_uniform(i::Int) = iid(Float64, c->uniform(c,0,1),i)
multivariate_normal(i::Int, j::Int) = iid(Float64, c->normal(c,0,1),i,j)
multivariate_normal(i::Int) = iid(Float64, c->normal(c,0,1),i)

MultivariateNormal
