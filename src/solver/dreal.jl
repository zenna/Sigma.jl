## Conversion of Sigma Function into DReal expression
## ==================================================

typealias DimToVar Dict{Int,DReal.Ex}

type DRealRandVar{T} <: RandVar{T}
  ex::DReal.Ex{T}
  ctx::DReal.Context
  dimtovar::DimToVar
end

dims(X::DRealRandVar) = Set{Int}(collect(keys(X.dimtovar)))

## Compie a Sigma Random Variable into a DReal Variable
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

function expand(X::ConstantRandVar, dimtovar::DimToVar, ctx::DReal.Context)
  X.val
end

function expand(X::OmegaRandVar, dimtovar::DimToVar, ctx::DReal.Context)
  dimtovar[X.dim]
end

for (name, op) in all_functional_randvars
  eval(
  quote
  # Real
  function expand(X::$name, dimtovar::DimToVar, ctx::DReal.Context)
    ($op)(ctx, [expand(arg,dimtovar,ctx) for arg in args(X)]...)
  end
  end)
end

# Returns an abstract bool
function call(X::DRealRandVar{Bool},ω::AbstractOmega{Float64})
  ctx = X.ctx
  debugstring = ASCIIString[]
  push_ctx!(ctx)
  # push!(debugstring, "(push 1)")

  ## Define subset (box) of Omega using assertions
  for dim in dims(ω)
    lb = (>=)(ctx, X.dimtovar[dim], ω[dim].l)
    ub = (<=)(ctx, X.dimtovar[dim], ω[dim].u)
    # push!(debugstring, "(assert",lb,")")
    DReal.add!(ctx,lb)
    # push!(debugstring, "(assert",ub,")")
    DReal.add!(ctx,ub)
  end
  # push!(debugstring, "(assert",X.ex,")")
  DReal.add!(ctx, X.ex)
  # push!(debugstring, "(check-sat)")

  ## 1. ∃ω ∈ A ∩ X : Does A contain any point X?
  pos_case = is_satisfiable(ctx)
  
  # push!(debugstring, "(pop 1)")
  pop_ctx!(ctx) #undo from 2 to here

  # push!(debugstring, "(push 1)")
  push_ctx!(ctx)
  for dim in dims(ω)
    lb = (>=)(ctx,X.dimtovar[dim],ω[dim].l)
    ub = (<=)(ctx,X.dimtovar[dim],ω[dim].u)
    # push!(debugstring, "(assert",lb,")")
    DReal.add!(ctx,lb)
    # push!(debugstring, "(assert",ub,")")
    DReal.add!(ctx,ub)
  end
  notex = (!)(ctx,X.ex)
  # push!(debugstring, "(assert", notex,")")
  DReal.add!(ctx, notex)

  # ∃ω ∈ A \ X : Does A contain any point not in X?
  # push!(debugstring, "(check-sat)")
  neg_case = is_satisfiable(ctx)

  # push!(debugstring, "(pop 1)")
  pop_ctx!(ctx)
  
  if pos_case & neg_case tf
  elseif pos_case t
  elseif neg_case f
  else
    # print(debugstring)
    error("Solver error: Query or its negation must be true")
  end
end
