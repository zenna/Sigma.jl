typealias RandVector{T} RandArray{T,1}
typealias RandMatrix{T} RandArray{T,2}

# ## Constructors
# ## ============
RandArray{T,N}(xs::Array{RandVar{T},N}) = RandArray{T,N}(xs)
RandArray(T::DataType, nrows::Int64) =
  RandArray{T,1}(Array(RandVar{T},nrows))
RandArray(T::DataType, nrows::Int64, ncols::Int64) =
  RandArray{T,2}(Array(RandVar{T},nrows,ncols))
RandArray{T<:Real}(a::Array{T}) = RandArray(Any[ConstantRandVar(x) for x in a])

RandArray{T<:SymbolicRandVar}(a::Array{T}) = RandArray(Any[a...])

# Fall back when type inference fails
function RandArray(xs::Array{Any,2})
  rtype = rangetype(xs[1,1])
  out = Array(RandVar{rtype},size(xs)...)
  for i = 1:size(xs,1)
    for j = 1:size(xs,2)
      @assert isa(xs[i,j],RandVar)
      @assert rangetype(xs[i,j]) == rtype "inconsistent types of random variables in array"
      out[i,j] = xs[i,j]
    end
  end
  RandArray(out)
end

# Fall back when type inference fails
function RandArray(xs::Array{Any,1})
  rtype = rangetype(xs[1])
  out = Array(RandVar{rtype},size(xs)...)
  for i = 1:size(xs,1)
    @assert isa(xs[i],RandVar)
    @assert rangetype(xs[i]) == rtype "inconsistent types of random variables in array"
    out[i] = xs[i]
  end
  RandArray(out)
end

# ## Conversion
# ## ==========
convert{T}(::Type{RandArray{T,2}}, arr::Matrix{T}) =
  RandArray(RandVar{T}[ConstantRandVar{T}(arr[i,j]) for i=1:size(arr,1), j = 1:size(arr,2)])
convert{T}(::Type{RandArray{T,1}}, arr::Vector{T}) = RandArray(RandVar{T}[ConstantRandVar{T}(a) for a in arr])
convert{T<:RandVar,N}(::Type{RandArray{T,N}}, A::Array{T,N}) = RandArray(A)
convert{T,N}(::Type{Array{RandVar{T},N}}, XS::RandArray{T,N}) = XS.array

convert{T, R<:RandVar}(::Type{Array{RandVar{T}}}, arr::Vector{R}) = RandVar{T}[arr...]
convert{T, R<:RandVar}(::Type{Array{RandVar{T}}}, arr::Matrix{R}) =
  RandVar{T}[arr[i,j] for i=1:size(arr,1), j = 1:size(arr,2)]

call{T}(Xs::RandArray{T,1}, ω::Omega) =
  [call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
call{T}(Xs::RandArray{T,2}, ω::Omega) =
  [call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]

# ## Array Access/Updating
# ## =====================
getindex(Xs::RandVector, i::Int64) = Xs.array[i]
getindex(Xs::RandMatrix, i::Int64, j::Int64) = Xs.array[i,j]
getindex(Xs::RandMatrix, i::Int64) = ((c,r) = divrem(i-1,size(Xs,1)); Xs.array[r+1,c+1])

setindex!(X::RandArray, Y, i::Real) = setindex!(X.array, Y, i)
setindex!(X::RandArray, Y::Sigma.RandArray, i::Real) = setindex!(X.array, Y.array, i)
setindex!(X::RandArray, Y::RandArray, is...) = setindex!(X.array, Y.array, is...)
setindex!(X::RandArray, Y, is...) = setindex!(X.array, Y, is...)

# setindex!{T}(X::RandVector,v::T,i::Int64) = X.array[i] = v
# setindex!{T}(X::RandArray,v::T,i::Int64,j::Int64) = X.array[i,j] = v

function setindex!{T}(X::RandArray{T,2}, Y::RandArray{T,2},
                      u::UnitRange{Int64}, i::Int64)
  setindex!(X.array, Y.array, u, i)
end

rangetype{T,N}(XS::RandArray{T,N}) = Array{T,N}
dims(XS::RandArray) = union(map(dims, XS.array)...)
ndims(XS::RandArray) = length(dims(XS))

size(Xs::RandArray, i::Int) = size(Xs.array, i)
size(Xs::RandArray) = size(Xs.array)
endof(Xs::RandArray) = endof(Xs.array)

getindex(Xs::RandMatrix, i::Int64, js::UnitRange{Int64}) = RandArray(Xs.array[i,js])
getindex(Xs::RandMatrix, is::UnitRange{Int64}, j::Int64) = RandArray(Xs.array[is,j])
getindex(Xs::RandMatrix, is::UnitRange{Int64}, js::UnitRange{Int64}) = RandArray(Xs.array[is,js])
getindex(Xs::RandVector, is::UnitRange{Int64}) = RandArray(Xs.array[is])

function getindex(Xs::RandVector, is::StepRange)
  Ys = RandArray(eltype(Xs),length(is))
  j = 1
  for i in is
    Ys[j] = Xs[i]
    j += 1
  end
  Ys
end

## Concats
hcat(Xs::RandArray, Ys::RandArray) =
  RandArray(hcat(Xs.array, Ys.array))

vcat(Xs::RandArray, Ys::RandArray) =
  RandArray(hcat(Xs.array, Ys.array))

# ## Iteration
start(Xs::RandArray) = start(Xs.array)
next(Xs::RandArray, state) = next(Xs.array, state)
done(Xs::RandArray, state) = done(Xs.array, state)

# # PERF: use list comprehensions for speed
function rand{T,N}(Xs::RandArray{T,N})
  ret::Array{T,N} = call(Xs,LazyRandomVector(Float64))
  return ret
end

## Arbitrary Array  Functions
@compat similar{T,N}(X::RandArray{T,N}, elem_type, dims::Tuple{Vararg{Int}}) = RandArray(T,dims...)
# @compat similar{T}(X::RandArray{T,1}, elem_type::Type{RandVar{Float64}}, dims::Tuple{Int64}) = RandArray(T)
# similar(::Sigma.RandArray{Float64,1}, ::Type{Sigma.RandVar{Float64}}, ::Tuple{Int64})

# ## Complex Array Functions
# ## =======================

# import Base:all
"Is every element in Xs true, returns Bool-valued RandVar"
function all{N}(Xs::RandArray{Bool,N})
  x = Xs[1]
  for i = 2:length(Xs)
    x &= Xs[i]
  end
  xs
end

# ## Arithmetic
# ## ==========

# Ambiguity Fixes
(.^){N}(::Base.MathConst{:e}, XS::RandArray{Base.MathConst{:e}, N}) = RandArray((.^)(e,XS.array))
(-){N}(x::Bool, Y::RandArray{Bool,N}) = convert(Int, x) - convert(RandVar{Int}, Y) #FIX ME TESTME: THis prolly doesn't work
(+){N}(x::Bool, Y::RandArray{Bool,N}) = convert(Int, x) + convert(RandVar{Int}, Y) #FIX ME TESTME: THis prolly doesn't work
(+){N}(Y::RandArray{Bool,N}, x::Bool) = convert(RandVar{Int}, Y) + convert(Int, x) #FIX ME TESTME: THis prolly doesn't work

# # Here, we extract the arrays of both args and apply op
for op = (:+, :-, :*, :.*, :/, :&, :|, :.^)
  @eval ($op){T<:Real}(XS::RandArray{T}, YS::RandArray{T}) = RandArray(($op)(XS.array,YS.array))
  # Interop with 'normal arrays' promote them to RandArrays
  @eval ($op){T<:Real,N}(XS::RandArray{T,N}, YS::Array{T,N}) = RandArray(($op)(XS.array,YS))
  @eval ($op){T<:Real,N}(YS::Array{T,N}, XS::RandArray{T,N}) = RandArray(($op)(YS,XS.array))

  # Point wise arithmetic against rand variable (first arg)
  @eval ($op){T<:Real,N}(Y::RandVar{T}, XS::RandArray{T,N}) = RandArray(map(x->($op)(Y,x), XS.array))
  @eval ($op){T<:Real,N}(y::T, XS::RandArray{T,N}) = ($op)(ConstantRandVar(y),XS)

  # Point wise arithmetic against rand variable (second arg)
  @eval ($op){T<:Real,N}(XS::RandArray{T,N}, Y::RandVar{T}) = RandArray(map(x->($op)(x,Y), XS.array))
  @eval ($op){T<:Real,N}(XS::RandArray{T,N}, y::T) = ($op)(XS,ConstantRandVar(y))
end

# Inequalities
for (array_op, elem_op) = ((:.>, :>), (:.>=, :>=), (:.<, :<), (:.<=, :<=), (:(.==), :(==)), (:.!=, :!=))
  @eval ($array_op){T,N}(XS::RandArray{T,N}, YS::RandArray{T,N}) =
    RandArray(map((x,y)->($elem_op)(x,y), XS.array,YS.array))
  # Interop with 'normal arrays' promote them to RandArrays
  @eval ($array_op){T,N}(XS::RandArray{T,N}, ys::Array{T,N}) = RandArray(map((x,y)->($elem_op)(x,y), XS.array,ys))
  @eval ($array_op){T,N}(ys::Array{T,N}, XS::RandArray{T,N}) = RandArray(map((x,y)->($elem_op)(y,x), ys,XS.array))
end

for op = (:(==), :!=)
  eval(
  quote
  function ($op){T,N}(XS::RandArray{T,N}, YS::RandArray{T,N})
    if size(XS) == size(YS)
      all([($op)(XS.array[i],YS.array[i]) for i = 1:length(XS)])
    else
      ConstantRandVar(false)
    end
  end

  function ($op){T,N}(XS::RandArray{T,N}, ys::Array{T,N})
    if size(XS) == size(ys)
      all([($op)(XS.array[i],ys[i]) for i = 1:length(XS)])
    else
      ConstantRandVar(false)
    end
  end

  function ($op){T,N}(ys::Array{T,N}, XS::RandArray{T,N})
    if size(XS) == size(ys)
      all([($op)(XS.array[i],ys[i]) for i = 1:length(XS)])
    else
      ConstantRandVar(false)
    end
  end
  end)
end

# Unary Functions
for op = (:transpose, :ctranspose)
  @eval ($op)(X::RandArray) = RandArray($op(X.array))
end

# Unary ElementWise Functions
for op = (:abs, :asin, :sqrt, :exp, :log, :cos, :sin, :tan, :acos, :asin, :atan,
          :cosh, :sinh, :tanh, :acosh, :asinh, :atanh, :abs, :atan2, :max, :min,
          :sign)
  @eval ($op){T,N}(X::RandArray{T,N}) = RandArray{Float64,N}(map($op,X.array))
end

function lambda{T}(XS::RandArray{T,2})
  X_fns = map(lambda,XS.array)
  ω -> [X_fns[i,j](ω) for i = 1:size(XS,1), j = 1:size(XS,2)]
end

function lambda{T}(XS::RandArray{T,1})
  X_fns = map(lambda,XS.array)
  ω -> [X_fns[i](ω) for i = 1:size(XS,1)]
end

function isapprox{T}(XS::RandArray{T}, ys::Array{T},epsilon = DEFAULT_PREC)
  sum(abs(XS - ys)) <= epsilon
end

function isapprox{T}(ys::Array{T}, XS::RandArray{T}, epsilon = DEFAULT_PREC)
  sum(abs(ys - XS)) <= epsilon
end

function isapprox{T}(XS::RandArray{T}, YS::RandArray{T}; epsilon = DEFAULT_PREC)
  sum(abs(XS - YS)) <= epsilon
end


## Ifelse
ifelse{T,N}(A::RandVar{Bool}, B::Array{T,N}, C::Array{T,N}) =
  RandArray(map((b,c)->ifelse(A,b,c),B,C))

ifelse{T,N}(A::RandVar{Bool}, B::RandArray{T,N}, C::Array{T,N}) =
  RandArray(map((b,c)->ifelse(A,b,c),B,C))

ifelse{T,N}(A::RandVar{Bool}, B::Array{T,N}, C::RandArray{T,N}) =
  RandArray(map((b,c)->ifelse(A,b,c),B,C))

print(io::IO, x::RandArray) = print(io, "what")
show(io::IO, x::RandArray) = show(io, "whats")

# print(io::IO, A::RandArray) = (print("YOU"); print(io, typeof(A),"\n",A.array))
# print(A::RandArray) = (print("ME"); print(A.array))
# println(A::RandArray) = (println("MES"); println(A.array))
# println(io::IO, A::RandArray) = (println("MESA"); println(io, A.array))
# show(io::IO, A::RandArray) = show(io, A.array)
# show(A::RandArray) = show(A.array)