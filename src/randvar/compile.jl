## Compile rand vars into callable functions
## =========================================
all_functional_randvars = union(real_real_real, real_real, real_floating,
                                real_real_bool, ((:IfElseRandVar, :ifelse),))
for (name,op) in all_functional_randvars
  eval(
  quote
  function convert(::Type{Expr}, X::$name)
    Expr(:call,$op,[convert(Expr,arg) for arg in args(X)]...)
  end
  end)
end

convert(::Type{Expr}, X::ConstantRandVar) = X.val
convert(::Type{Expr}, X::OmegaRandVar) = :(ω[$(X.dim)])
lambda_expr(X::RandVar) = Expr(:(->),:ω,convert(Expr,X))
lambda(X::RandVar) = eval(lambda_expr(X))
