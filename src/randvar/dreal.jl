## Conversion of Sigma Function into dReal expression
## ==================================================

typealias DimToVar Dict{Int,dReal.Ex}

type DRealRandVar{T} <: RandVar{T}
  ex::dReal.Ex{T}
  ctx::dReal.Context
  dimtovar::DimToVar
end

## Compie a Sigma Random Variable into a dReal Variable
function convert{T}(::Type{DRealRandVar{T}}, X::RandVar{T})
  ctx = Context(qf_nra)

  # Create dict of dimension to variable so we don't
  # try to recreate variables when doing expansion (cause error in dreal)
  dimtovar = DimToVar()
  for dim in dims(X)
    dimtovar[dim] = Var(ctx, Float64,"omega$(dim)",0.0,1.0)
  end
  ex = expand(X, dimtovar, ctx)
  DRealRandVar{T}(ex,ctx,dimtovar)
end

function expand(X::ConstantRandVar, dimtovar::DimToVar, ctx::dReal.Context)
  X.val
end

function expand(X::OmegaRandVar, dimtovar::DimToVar, ctx::dReal.Context)
  dimtovar[X.dim]
end

for (name, op) in all_functional_randvars
  eval(
  quote
  # Real
  function expand(X::$name, dimtovar::DimToVar, ctx::dReal.Context)
    ($op)(ctx, [expand(arg,dimtovar,ctx) for arg in args(X)]...)
  end
  end)
end

# Returns an abstract bool
function call(X::DRealRandVar{Bool},ω::AbstractOmega{Float64})
  # 1. ∃ω ∈ A ∩ X : Does A contain any point X?
  ctx = X.ctx
  push_ctx!(ctx) #1
  println("(push 1)")
  for dim in dims(ω)
#     @show dim
    lb = (>=)(ctx,X.dimtovar[dim],ω[dim].l)
    ub = (<=)(ctx,X.dimtovar[dim], ω[dim].u)
    println("(assert",lb,")")
    dReal.add!(ctx,lb)
    println("(assert",ub,")")
    dReal.add!(ctx,ub)
  end
#   push_ctx!(ctx) #2
  println("(assert",X.ex,")")
  dReal.add!(ctx, X.ex)
#   println("About to check pop case")
  println("(check-sat)")
  pos_case = is_satisfiable(ctx)
#   @show pos_case
  println("(pop 1)")
  pop_ctx!(ctx) #undo from 2 to here
#   println("About to push")
  println("(push 1)")
  push_ctx!(ctx) #3
  for dim in dims(ω)
#     @show dim
    lb = (>=)(ctx,X.dimtovar[dim],ω[dim].l)
    ub = (<=)(ctx,X.dimtovar[dim],ω[dim].u)
    println("(assert",lb,")")
    dReal.add!(ctx,lb)
    println("(assert",ub,")")
    dReal.add!(ctx,ub)
  end
#   println("About to check neg case")
  notex = (!)(ctx,X.ex)
  println("(assert",notex,")")
  dReal.add!(ctx, notex)

  # 2. ∃ω ∈ A \ X : Does A contain any point not in X?
  println("(check-sat)")
  neg_case = is_satisfiable(ctx)
#   @show pos_case
  println("(pop 1)")
  println("; end")
  pop_ctx!(ctx) #roll back to 3
#   pop_ctx!(ctx) #roll back to 1
  if pos_case & neg_case tf
  elseif pos_case t
  elseif neg_case f
  else
    error("Query or its negation must be true")
  end
end
