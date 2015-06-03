 @doc """An array of random variables (and also a random variable itself)
  `T` is the range type of elements (e.g for multivariate normal, T = Float64)
  `N` is the dimensionality of array""" ->
type PureRandArray{T,N} <: DenseArray{RandVar{T},N}
  array::Array{RandVar{T},N}
end

# rangetype{R<:RandVar}(xs::Array{R}) = rangetype(eltype(xs))

typealias PureRandVector{T} PureRandArray{T,1}
typealias PureRandMatrix{T} PureRandArray{T,2}

# ## Constructors
# ## ============
PureRandArray{T,N}(xs::Array{RandVar{T},N}) = PureRandArray{T,N}(xs)
PureRandArray(T::DataType, nrows::Int64) =
  PureRandArray{T,1}(Array(RandVar{T},nrows))
PureRandArray(T::DataType, nrows::Int64, ncols::Int64) =
  PureRandArray{T,2}(Array(RandVar{T},nrows,ncols))

# Fall back when type inference fails
function PureRandArray(xs::Array{Any,2})
  rtype = rangetype(xs[1,1])
  out = Array(RandVar{rtype},size(xs)...)
  for i = 1:size(xs,1)
    for j = 1:size(xs,2)
      @assert isa(xs[i,j],RandVar)
      @assert rangetype(xs[i,j]) == rtype "inconsistent types of random variables in array"
      out[i,j] = xs[i,j]
    end
  end
  PureRandArray(out)
end

# Fall back when type inference fails
function PureRandArray(xs::Array{Any,1})
  rtype = rangetype(xs[1])
  out = Array(RandVar{rtype},size(xs)...)
  for i = 1:size(xs,1)
    @assert isa(xs[i],RandVar)
    @assert rangetype(xs[i]) == rtype "inconsistent types of random variables in array"
    out[i] = xs[i]
  end
  PureRandArray(out)
end

# ## Conversion
# ## ==========
convert{T}(::Type{PureRandArray{T,2}}, arr::Matrix{T}) =
  PureRandArray(RandVar{T}[ConstantRandVar{T}(arr[i,j]) for i=1:size(arr,1), j = 1:size(arr,2)])
convert{T}(::Type{PureRandArray{T,1}}, arr::Vector{T}) = PureRandArray(RandVar{T}[ConstantRandVar{T}(a) for a in arr])
convert{T<:RandVar,N}(::Type{PureRandArray{T,N}}, A::Array{T,N}) = PureRandArray(A)

convert{T, R<:RandVar}(::Type{Array{RandVar{T}}}, arr::Vector{R}) = RandVar{T}[arr...]
convert{T, R<:RandVar}(::Type{Array{RandVar{T}}}, arr::Matrix{R}) =
  RandVar{T}[arr[i,j] for i=1:size(arr,1), j = 1:size(arr,2)]

# B = map(x->ConstantRandVar{Float64}(x),A)
# C = convert(Array{RandVar{Float64}}, B)

# A = [1,2,.3]
# B = mvuniform(0,10,3)
# rand(A + B)
# Q = A + B.array
# rangetype(Q[3])
# PureRandArray(Q)


# B + A
# A + mvuniform(0,0,10,3)


# # PureRandArray(B)
# convert(PureRandArray{Float64,1}, [1.,2,3])


# convert{T,N}(::Type{PureRandArray{T,N}}, A::Array{T,N}) = PureRandArray{T,N,R}(map(a->convert(R,a),A))
# promote_rule{T,N,R}(::Type{PureRandArray{T,N,R}}, ::Type{Array{T,N}}) =
#   PureRandArray{T,N,R}

# rangetype(Xs::PureRandArray) = Array{typeof(Xs).parameters[1]}
# eltype(Xs::PureRandArray) = rangetype(Xs).parameters[1]
call{T,O<:Omega}(Xs::PureRandArray{T,1}, ω::O) =
  T[call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::PureRandArray{T,2}, ω::Omega) =
  T[call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

# ## Array Access/Updating
# ## =====================
getindex(Xs::PureRandVector, i::Int64) = Xs.array[i]
getindex(Xs::PureRandMatrix, i::Int64, j::Int64) = Xs.array[i,j]
getindex(Xs::PureRandMatrix, i::Int64) = ((c,r) = divrem(i-1,size(Xs,1)); Xs.array[r+1,c+1])

setindex!{T}(X::PureRandVector,v::T,i::Int64) = X.array[i] = v
setindex!{T}(X::PureRandArray,v::T,i::Int64,j::Int64) = X.array[i,j] = v

ndims{T,N}(Xs::PureRandArray{T,N}) = N
size(Xs::PureRandArray, i::Int) = size(Xs.array, i)
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

# ## Iteration
start(Xs::PureRandArray) = start(Xs.array)
next(Xs::PureRandArray, state) = next(Xs.array, state)
done(Xs::PureRandArray, state) = done(Xs.array, state)

# # PERF: use list comprehensions for speed
function rand{T,N}(Xs::PureRandArray{T,N})
  ret::Array{T,N} = call(Xs,LazyRandomVector(Float64))
  return ret
end

## Arbitrary Array  Functions
similar{T}(X::PureRandArray{T,2}, elem_type, dims::Tuple{Int,Int}) = PureRandArray(T,dims...)

# ## Complex Array Functions
# ## =======================
# function dot{T,R}(A::PureRandVector{T,R},B::PureRandVector{T,R})
#   @assert length(A.array) == length(B.array)
#   array = [A.array[i] * B.array[i] for i = 1:length(A.array)]
#   sum(array)::R{Float64}
# end

# import Base:all
@doc "Is every element in Xs true, returns Bool-valued RandVar" ->
function all{N}(Xs::PureRandArray{Bool,N})
  x = Xs[1]
  for i = 2:length(Xs)
    x &= Xs[i]
  end
  x
end

# @doc "Is p(every element in Xs) true, returns Bool-valued RandVar" ->
# function all{T,N,R}(p::Function, Xs::PureRandArray{T,N,R})
#   x = p(Xs[1])
#   for i = 2:length(Xs)
#     x &= p(Xs[i])
#   end
#   x
# end

# ## Arithmetic
# ## ==========

# # Here, we extract the arrays of both args and apply op
for op = (:+, :-, :*, :.*, :/, :&, :|, :.^)
  @eval ($op){T<:Real,N}(XS::PureRandArray{T,N}, YS::PureRandArray{T,N}) = PureRandArray(($op)(XS.array,YS.array))
  # Interop with 'normal arrays' promote them to RandArrays
  @eval ($op){T<:Real,N}(XS::PureRandArray{T,N}, YS::Array{T,N}) = PureRandArray(($op)(XS.array,YS))
  @eval ($op){T<:Real,N}(YS::Array{T,N}, XS::PureRandArray{T,N}) = PureRandArray(($op)(YS,XS.array))

  # Point wise arithmetic against rand variable (first arg)
  @eval ($op){T<:Real,N}(Y::RandVar{T}, XS::PureRandArray{T,N}) = PureRandArray(map(x->($op)(Y,x), XS.array))
  @eval ($op){T<:Real,N}(y::T, XS::PureRandArray{T,N}) = ($op)(ConstantRandVar(y),XS)

  # Point wise arithmetic against rand variable (second arg)
  @eval ($op){T<:Real,N}(XS::PureRandArray{T,N}, Y::RandVar{T}) = PureRandArray(map(x->($op)(x,Y), XS.array))
  @eval ($op){T<:Real,N}(XS::PureRandArray{T,N}, y::T) = ($op)(XS,ConstantRandVar(y))
end

# Inequalities
for (array_op, elem_op) = ((:.>, :>), (:.>=, :>=), (:.<, :<), (:.<=, :<=), (:(.==), :(==)), (:.!=, :!=))
  @eval ($array_op){T,N}(XS::PureRandArray{T,N}, YS::PureRandArray{T,N}) =
    PureRandArray(map((x,y)->($elem_op)(x,y), XS.array,YS.array))
  # Interop with 'normal arrays' promote them to RandArrays
  @eval ($array_op){T,N}(XS::PureRandArray{T,N}, ys::Array{T,N}) = PureRandArray(map((x,y)->($elem_op)(x,y), XS.array,ys))
  @eval ($array_op){T,N}(ys::Array{T,N}, XS::PureRandArray{T,N}) = PureRandArray(map((x,y)->($elem_op)(y,x), ys,XS.array))
end

for op = (:(==), :!=)
  eval(
  quote
  function ($op){T,N}(XS::PureRandArray{T,N}, YS::PureRandArray{T,N})
    if size(X) == size(Y)
      all([($op)(X.array[i],Y.array[i]) for i = 1:length(X)])
    else
      ConstantRandVar(false)
    end
  end

  function ($op){T,N}(XS::PureRandArray{T,N}, ys::Array{T,N})
    if size(XS) == size(ys)
      all([($op)(XS.array[i],ys[i]) for i = 1:length(XS)])
    else
      ConstantRandVar(false)
    end
  end

  function ($op){T,N}(ys::Array{T,N}, XS::PureRandArray{T,N})
    if size(XS) == size(ys)
      all([($op)(XS.array[i],ys[i]) for i = 1:length(XS)])
    else
      ConstantRandVar(false)
    end
  end
  end)
end

# Unary Functions
for op = (:abs, :asin, :sqrt, :exp, :log, :cos, :sin, :tan, :acos, :asin, :atan,
          :cosh, :sinh, :tanh, :acosh, :asinh, :atanh, :abs, :atan2, :max, :min,
          :sign)
  @eval ($op){T,N}(X::PureRandArray{T,N}) = PureRandArray{Float64,N}(map($op,X.array))
end

function lambda{T}(XS::PureRandArray{T,2})
  X_fns = map(lambda,XS.array)
  ω -> [X_fns[i,j](ω) for i = 1:size(XS,1), j = 1:size(XS,2)]
end

function lambda{T}(XS::PureRandArray{T,1})
  X_fns = map(lambda,XS.array)
  ω -> [X_fns[i](ω) for i = 1:size(XS,1)]
end

print(io::IO, A::PureRandArray) = print(typeof(A),"\n",A.array)
