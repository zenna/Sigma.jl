typealias MethodMap Dict{Expr, Expr}

# TODO
# Different typpe for Omega


@doc """A representation of a RandomVariable which supports function definitions.
  It does this by containing a shared method map.
  The body of a RandVarMM is always a functional definition
  The method map is a table mapping names to functional definitions""" ->
type RandVarMM{T} <: RandVar{T}
  body::Expr
  mm::MethodMap
  dims::Set{Int}
  compiled::Bool
  λ::Function
  RandVarMM(body, mm, dims, compiled, λ) = new(body, mm, dims, compiled, λ)
  RandVarMM(body, mm, dims) = new(body, mm, dims, false)
end

dims(X::RandVarMM) = X.dims
rangetype(X::RandVarMM) = typeof(X).parameters[1]
isequal(X::RandVarMM,Y::RandVarMM) = isequal(X.body.head,Y.body.head) && isequal(X.body.args, Y.body.args)

## Primitive Functions
## ===================
@compat randomega(i) =
  RandVarMM{Float64}(:(ω[$i]), Dict(:(rand(i)) => :(ω->ω[i])), Set(i))
israndomega(X::RandVarMM) = X.body.head == :ref && X.body.args[1] == :ω
randomegadim(X::RandVarMM) = X.body.args[2]

## Arithmetic
## ==========
@doc """
  Pointwise Lifting - arbitrary arity
  """ ->
function lift(op,RETURNT::DataType,args...)
  randvars = collect(filter(arg->isa(arg,RandVarMM), args))
  newbody = Expr(:call, op, args...)
  combined_mm = merge([rv.mm for rv in randvars]...)
  combined_dims = union([X.dims for X in randvars]...)
  RandVarMM{RETURNT}(newbody,combined_mm,combined_dims)
end

# Fix ambiguities
(^){T1<:Real,T2<:Integer}(X::RandVarMM{T1},c::T2) = lift(^,promote_type(T1, T2),X,c)

## Real × Real -> Real ##
for op = (:+, :-, :*, :/, :(^))
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarMM{T1}, Y::RandVarMM{T2}) = lift($op,promote_type(T1, T2),X,Y)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarMM{T1}, c::T2) = lift($op,promote_type(T1, T2),X,c)
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarMM{T2}) = lift($op,promote_type(T1, T2),c,X)
end

for op = (:abs,:-,:+)
  @eval ($op){T<:Real}(X::RandVarMM{T}) = lift($op,T,X,Y)
end

## Real -> Real ##
for op = (:exp, :log, :sin, :cos, :tan, :asin, :acos,:atan, :sinh, :cosh,:tanh, :atan2)
  @eval ($op){T<:Real}(X::RandVarMM{T}, RTYPE::DataType = Float64) = lift($op,RTYPE,X,Y)
end

## Real × Real -> Bool ##
for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarMM{T1}, Y::RandVarMM{T2}) = lift($op,Bool,X,Y)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarMM{T1}, c::T2) = lift($op,Bool,X,c)
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarMM{T2}) = lift($op,Bool,c,X)
end

## Real × Real -> Bool ##
for op = (:&, :|)
  @eval ($op)(X::RandVarMM{Bool}, Y::RandVarMM{Bool}) = lift($op,Bool,X,Y)
  @eval ($op)(X::RandVarMM{Bool}, c::Bool) = lift($op,Bool,X,c)
  @eval ($op)(c::Bool, X::RandVarMM{Bool}) = lift($op,Bool,c,X)
end

## Bool -> Bool ##
!(X::RandVarMM{Bool})= lift(!,Bool,X)

## ifelse
ifelse{T}(A::RandVarMM{Bool}, B::RandVarMM{T}, C::RandVarMM{T}) =
  lift(ifelse,T,A,B,C)

ifelse{T1<:Real}(A::RandVarMM{Bool}, B::T1, C::T1) =
  lift(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarMM{Bool}, B::RandVarMM{T1}, C::T1) =
  lift(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarMM{Bool}, B::T1, C::RandVarMM{T1}) =
  lift(ifelse,T1,A,B,C)

## Conversion
## =========

# What is the topmost function operator of a random variable
func(X::RandVarMM) = X.body.args[1]
# What are the function arguments of the random variable
args(X::RandVarMM) = X.body.args[2:end]


# Find the image of a predicate randvar with subset of Ω
call{T<:Real}(X::RandVarMM{Bool}, ω::Omega{T}; solver = global_dreal()) =
  call(solver, X, ω)

# TODO
# @doc """Apply a random variable X to a point ω ∈ Ω in the sample space""" ->
# function call(X::RandVarMM, ω::Omega{Float64})

# # TODO
# @doc """Given all the randomness defined by ω, what is the likelihood of the corresponding
#   program trace of X""" ->
# function likelihood(X::RandVarMM, ω::Omega{Float64}, )
# end
