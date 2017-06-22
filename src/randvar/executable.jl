## Compile rand vars into callable functions
## =========================================

dims(X::JuliaRandVar) = X.dims

"Evaluate a random variable on an element of scenario ω"
(X::JuliaRandVar)(ω::Omega) = Base.invokelatest(X.func, ω)

"Compile SymbolicRandVar into JuliaRandVar"
convert{T}(::Type{JuliaRandVar{T}}, X::SymbolicRandVar{T}) =
  JuliaRandVar{T}(compile(X), dims(X))

all_functional_randvars = union(real_real_real, real_real, real_floating,
                                real_real_bool, ((:IfElseRandVar, :ifelse),),
                                bool_bool_bool, ((:NotRandVar, :!),))
for (name,op) in all_functional_randvars
  eval(
  quote
  function convert(::Type{Expr}, X::$name)
    Expr(:call, $op, [convert(Expr, arg) for arg in args(X)]...)
  end
  end)
end

convert(::Type{Expr}, X::ConstantRandVar) = X.val
convert(::Type{Expr}, X::OmegaRandVar) = :(ω[$(X.dim)])

"lambda `Expr` of `X` e.g., `ω -> w * b + c`"
lambda_expr(X::SymbolicRandVar) = Expr(:(->), :ω,convert(Expr,X))

"Compile `X` into Julia lambda"
compile(X::SymbolicRandVar)::Function = eval(lambda_expr(X))

"Convert Elementary `X` to `ω -> quantile_X(ω)`"
function convert{T <: ElementaryRandVar}(::Type{Expr}, X::T)
  params = [convert(Expr, arg) for arg in args(X)]
  Expr(:call, :quantile, distribution_type(T), :(ω[$X.dim]), params...)
end

"Convert a random variable into an executable random variable"
executionalize{T}(X::RandVar{T}) = convert(JuliaRandVar{T}, X)
