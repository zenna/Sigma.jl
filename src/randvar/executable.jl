## Compile rand vars into callable functions
## =========================================

dims(X::ExecutableRandVar) = X.dims
call(X::ExecutableRandVar, ω::Omega) = X.func(ω)
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