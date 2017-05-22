## Compile rand vars into callable functions
## =========================================

# There are two kinds of input a random variable may take as input
# 1. A event, a subset of the sample space
# 2. A psuedo-event which is a subset of a transformed sample space, e.g. U(0,10)

## Situation 1. Normal Sample Space
## ================================

dims(X::ExecutableRandVar) = X.dims
(X::ExecutableRandVar)(ω::Omega) = X.func(ω)
convert{T}(::Type{ExecutableRandVar{T}}, X::SymbolicRandVar{T}) =
  ExecutableRandVar{T}(lambda(X), dims(X))

all_functional_randvars = union(real_real_real, real_real, real_floating,
                                real_real_bool, ((:IfElseRandVar, :ifelse),),
                                bool_bool_bool, ((:NotRandVar, :!),))
for (name,op) in all_functional_randvars
  eval(
  quote
  function convert(::Type{Expr}, X::$name)
    Expr(:call,$op,[convert(Expr,arg) for arg in args(X)]...)
  end
  end)
end

convert(::Type{Expr}, X::ConstantRandVar) = X.val
#add one for julia/c++ indexing mismatch, basically a HACK
convert(::Type{Expr}, X::OmegaRandVar) = :(ω[$(X.dim)])
lambda_expr(X::SymbolicRandVar) = Expr(:(->),:ω,convert(Expr,X))
lambda(X::SymbolicRandVar) = eval(lambda_expr(X))

function convert{T <: ElementaryRandVar}(::Type{Expr}, X::T)
  Expr(:call, :quantile, distribution_type(T), :(ω[$X.dim]), [convert(Expr, arg) for arg in args(X)]...)
end

## Situation 2. Psuedo-Sample space
## ================================
# What kind of this is this new space, is it too  a sample space.
# - well it's certainly not bounded between 0 and 1
# - and it doesn't have a uniform measure
# - What happens if you do uniform(0,0,10) and uniform(0,0,20) we'll get two dimensions
# - sometings which are UNSAt could be deemed SAT,
# - So we should only allow one, in a way it really is constructing a new sample space.

convert_psuedo{T}(::Type{ExecutableRandVar{T}}, X::SymbolicRandVar{T}) =
  ExecutableRandVar{T}(lambda_psuedo(X), dims(X))

for (name,op) in all_functional_randvars
  eval(
  quote
  function convert_psuedo(::Type{Expr}, X::$name)
    Expr(:call,$op,[convert_psuedo(Expr,arg) for arg in args(X)]...)
  end
  end)
end

convert_psuedo(::Type{Expr}, X::ConstantRandVar) = X.val
#add one for julia/c++ indexing mismatch, basically a HACK
convert_psuedo(::Type{Expr}, X::OmegaRandVar) = :(ω[$(X.dim)])
lambda_psuedo_expr(X::SymbolicRandVar) = Expr(:(->),:ω,convert_psuedo(Expr,X))
lambda_psuedo(X::SymbolicRandVar) = eval(lambda_psuedo_expr(X))

# This is the only difference
convert_psuedo{T <: ElementaryRandVar}(::Type{Expr}, X::T) = :(ω[$(X.dim)])

## Rand Array
## ==========
function convert{T}(::Type{ExecutableRandArray{T}}, Xs::RandArray{T,1})
  ExecutableRandArray([convert(ExecutableRandVar{T}, Xs.array[i]) for i = 1:size(Xs.array,1)])
end

function convert{T}(::Type{ExecutableRandArray{T}}, Xs::RandArray{T,2})
  ExecutableRandArray([convert(ExecutableRandVar{T}, Xs.array[i,j]) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)])
end

function convert_psuedo{T}(::Type{ExecutableRandArray{T}}, Xs::RandArray{T,1})
  ExecutableRandArray([convert_psuedo(ExecutableRandVar{T}, Xs.array[i]) for i = 1:size(Xs.array,1)])
end

function convert_psuedo{T}(::Type{ExecutableRandArray{T}}, Xs::RandArray{T,2})
  ExecutableRandArray([convert_psuedo(ExecutableRandVar{T}, Xs.array[i,j]) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)])
end

function (Xs::ExecutableRandArray{T,1}){T}(ω::Omega)
  T[call(Xs.array[i],ω) for i = 1:size(Xs.array,1)]
end

function (Xs::ExecutableRandArray{T,2}){T}(ω::Omega)
  T[call(Xs.array[i,j],ω) for i = 1:size(Xs.array,1), j = 1:size(Xs.array,2)]
end

## Executionalize
executionalize{T,N}(Xs::RandArray{T,N}) = convert_psuedo(ExecutableRandArray{T}, Xs)

executionalize{T}(X::RandVar{T}) = convert_psuedo(ExecutableRandVar{T}, X)
