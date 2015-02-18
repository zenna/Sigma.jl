import Base.eltype
import Base.size

type PureRandArray{T,N,R <: RandVar} <: RandVar{Array{T,N}}
  array::Array{R,N}
end

typealias PureRandVector{T,R} PureRandArray{T,1,R}
typealias PureRandMatrix{T,R} PureRandArray{T,2,R}
typealias LA{T,N,R} Union(Array{T,N}, PureRandArray{T,N,R}) #Lifted

## Constructors
## ============
rangetype{R<:RandVar}(xs::Array{R}) = rangetype(eltype(xs))
PureRandArray{R<:RandVar,N}(xs::Array{R,N}) = PureRandArray{rangetype(xs),N,R}(xs)
PureRandArray(T::DataType, nrows::Int64) =
  PureRandArray{T,1}(Array(RandVar{T},nrows))
PureRandArray(T::DataType, nrows::Int64, ncols::Int64) =
  PureRandArray{T,2}(Array(RandVar{T},nrows,ncols))

## Conversion
## ==========
convert{T,N,R}(::Type{PureRandArray{T,N,R}}, A::Array{R,N}) = PureRandArray{T,N,R}(A)
convert{T,N,R}(::Type{PureRandArray{T,N,R}}, A::Array{R,N}) = PureRandArray{T,N,R}(A)
convert{T,N,R}(::Type{PureRandArray{T,N,R}}, A::Array{T,N}) =
  PureRandArray{T,N,R}(map(a->convert(R,a),A))
promote_rule{T,N,R}(::Type{PureRandArray{T,N,R}}, ::Type{Array{T,N}}) =
  PureRandArray{T,N,R}

rangetype(Xs::PureRandArray) = Array{typeof(Xs).parameters[1]}
eltype(Xs::PureRandArray) = rangetype(Xs).parameters[1]
call{T}(Xs::PureRandArray{T,1}, ω) =
  [call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::PureRandArray{T,2}, ω) =
  [call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

# Hacks to return correct type when ω is SampleOmega
# Julia 0.4 should make this unnecessary due to better type inference
call{T}(Xs::PureRandArray{T,1}, ω::SampleOmega) =
  T[call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::PureRandArray{T,2}, ω::SampleOmega) =
  T[call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

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

## Concats
hcat(Xs::PureRandArray, Ys::PureRandArray) =
  PureRandArray(hcat(Xs.array, Ys.array))

vcat(Xs::PureRandArray, Ys::PureRandArray) =
  PureRandArray(hcat(Xs.array, Ys.array))

## Array Access - Int-RandVar indices
## ==================================

# access{T}(X::PureRandVector{T},i::Int,ω) = call(X[i],ω)
# access{T}(X::PureRandVector{T},i::Interval,ω) =
#   ⊔([call(X[j],ω) for j = int(i.l):int(i.u)])

# getindex{T}(Xs::PureRandVector{T}, I::RandVarSymbolic{Int}) =
#   RandVarSymbolic{T}(:(access($Xs,call($I,ω),ω)))

## Iteration
start(Xs::PureRandArray) = start(Xs.array)
next(Xs::PureRandArray, state) = next(Xs.array, state)
done(Xs::PureRandArray, state) = done(Xs.array, state)

## Primitive Array Functions
## =========================
# PERF: anon function calls are slow
# sum{T}(Xs::PureRandArray{T}, ω) = sum(map(x->call(x,ω), Xs.array))
sum{T}(Xs::PureRandArray{T}, ω) = sum(call(Xs,ω))
#   sum(map(x->call(x,ω), Xs.array))

sum{T,N,R<:RandVarSymbolic}(Xs::PureRandArray{T,N,R}) =
  RandVarSymbolic(T,:(sum($Xs,ω)))
# sum{T}(Xs::PureRandArray{T}) = RandVarSymbolic(T,:(sum($Xs,ω)))

# In principle length(Xs) should return a Int-RandVar, but until
# we support indexing on integer random variables it makes things hard
# / inconvenient, so leave this commented
# length(Xs::PureRandArray) = RandVarSymbolic(Int64,:(length($Xs.array)))
length(Xs::PureRandArray) = length(Xs.array)
size(Xs::PureRandArray) = size(Xs.array)
size(Xs::PureRandArray,i::Int) = size(Xs.array, i)

# PERF: use list comprehensions for speed
function rand{T,N,R<:RandVarSymbolic}(Xs::PureRandArray{T,N,R})
  ret::Array{T,N} = call(Xs,SampleOmega())
  return ret
end

## Complex Array Functions
## =======================
function dot{T,R}(A::PureRandVector{T,R},B::PureRandVector{T,R})
  @assert length(A.array) == length(B.array)
  array = [A.array[i] * B.array[i] for i = 1:length(A.array)]
  sum(array)::R{Float64}
end

## Arithmetic
## ==========

# Here, we extract the arrays of both args and apply op
# An alternative is to have a RandVarSymbolic which
# Only when called with an omega will do the array computations on abstract values
# this may be preferable
for op = (:+, :-, :*, :.*, :/, :&, :|)
  @eval begin
    function ($op){T,D}(X::PureRandArray{T,D}, Y::PureRandArray{T,D})
      let op = $op
        PureRandArray(($op)(X.array,Y.array))
      end
    end

    # Interop with 'normal arrays' promote them to RandArrays
    function ($op){T,D,R}(X::PureRandArray{T,D,R}, Y::Array{T,D})
      a::Array{R} = ($op)(X.array,Y)
      PureRandArray(a)
    end

    function ($op){T,D,R}(Y::Array{T,D}, X::PureRandArray{T,D,R})
      a::Array{R} = ($op)(Y,X.array)
      PureRandArray(a)
    end
#     ($op){T,D,R}(X::Array{T,D}, Y::PureRandArray{T,D,R}) = PureRandArray(($op)(X,Y.array))

    # Point wise arithmetic against rand variable (first arg)
    function ($op){T,D,R,T2<:Real}(Y::RandVar{T2}, X::PureRandArray{T,D,R})
      let op = $op
        PureRandArray(map(x->($op)(Y,x), X.array))
      end
    end

    # Point wise arithmetic against rand variable (second arg)
    function ($op){T,D,R,T2<:Real}(X::PureRandArray{T,D,R}, Y::RandVar{T2})
      let op = $op
        PureRandArray(map(x->($op)(x,Y), X.array))
      end
    end

#     ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
#     ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:(==), :!=, :isapprox)
  @eval begin
    function ($op){T,D,R}(X::PureRandArray{T,D,R}, Y::PureRandArray{T,D,R})
      @assert size(X) == size(Y)
      all([X.array[i] == Y.array[i] for i = 1:length(X)])
    end

    function ($op){T,D,R}(X::PureRandArray{T,D,R}, Y::Array{T,D})
      @assert size(X) == size(Y)
      all([X.array[i] == Y[i] for i = 1:length(X)])
    end

    function ($op){T,D,R}(Y::Array{T,D}, X::PureRandArray{T,D,R})
      @assert size(X) == size(Y)
      all([X.array[i] == Y[i] for i = 1:length(X)])
    end
  end
end

# Unary Functions
for op = (:abs,)
  @eval begin
  function ($op){T,D}(X::PureRandArray{T,D})
    PureRandArray(map($op,X.array)) #PERF
  end
  end
end

## Independent RandVars
## ====================
function iidall(T::DataType, R::DataType, c::Function,
             nrows::Int64, ncols::Int64; offset::Int64 = 0)
  a::Array{R{T}} = [c(i+(j-1)*(nrows) + offset) for i = 1:nrows, j = 1:ncols]
  PureRandArray{T,2,R{T}}(a)
end

function iidall(T::DataType, R::DataType, c::Function, nrows::Int64; offset = 0)
  v::Array{R{T}} = [c(i + offset) for i = 1:nrows]
  PureRandVector{T,R{T}}(v)
end

iidmeta(T::DataType, c, nrows, ncols; offset...) = iidall(T, RandVarMeta, c, nrows, ncols; offset...)
iidmeta(T::DataType, c, nrows; offset...) = iidall(T, RandVarMeta, c, nrows; offset...)

iidsmt(T::DataType, c, nrows, ncols; offset...) = iidall(T, RandVarSMT, c, nrows, ncols; offset...)
iidsmt(T::DataType, c, nrows; offset...) = iidall(T, RandVarSMT, c, nrows; offset...)

iidai(T::DataType, c, nrows, ncols; offset...) = iidall(T, RandVarSymbolic, c, nrows, ncols; offset...)
iidai(T::DataType, c, nrows; offset...) = iidall(T, RandVarSymbolic, c, nrows; offset...)

