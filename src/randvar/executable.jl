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


## For Random Variables

convert(::Type{Distributions.Normal}, X::NormalRandVar) = 
  Distributions.Normal(X.μ.val, X.σ.val)

function convert(::Type{Expr}, X::NormalRandVar)
  if isa(X.μ, ConstantRandVar) && isa(X.σ, ConstantRandVar)
    x_dist = convert(Distributions.Normal, X)
    Expr(:call, :quantile, x_dist, X.dim, :ω)
  else
    error("RandVar Parameters unsupported")
  end
end

"Computes quantile of interval, quantile is monotonic function so its easy"
function quantile{T}(X::Distributions.Distribution, p::Interval{T})
  # Quantiles must be between 0 and 1
  p_valid = intersect(p, unit(p))
  lb = quantile(X, p_valid.l)
  ub = quantile(X, p_valid.u)
  Interval{T}(lb, ub)
end

quantile(X::Distributions.Distribution, i::Id, ω::Omega) = quantile(X, ω[i])