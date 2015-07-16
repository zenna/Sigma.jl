# Mapping from variable SymbolicRandVars to DReal Ex{}
typealias SymbToVar Dict{SymbolicRandVar, DReal.Ex}

"A Random variable represented as a expression in DReal"
type DRealRandVar{T} <: RandVar{T}
  ex::DReal.Ex{T}       # The random variable
  ctx::DReal.Context    # Contet
  sym_to_var::SymbToVar
end

dims(X::DRealRandVar) = union(map(dims, keys(X.sym_to_var))...)::Set{Int}

## Conversion between Symbolic RandVar and Dreal expression
## ========================================================

# The general rules are
# 1. If I'm a composite RandVar then expand all my children
# 2. If I'm an elementary randvar with constant arguments, do the interval trick
# 3. If I'm an elementary randvar with random parameters and closed fom quantile, then treat as 1
# 4. If I'm an elementary randvar with random parameters and no-closed form quantile then treat children as 1 and me as 1

"Construct DReal.RandVar from Symbolic RandVar"
function convert{T}(::Type{DRealRandVar{T}}, X::SymbolicRandVar{T})
  ctx = Context(qf_nra)
  sym_to_var = SymbToVar()
  ex = expand(X, sym_to_var, ctx)
  DRealRandVar(ex, ctx, sym_to_var)
end

# 1. If I'm a composite RandVar then expand all my children
for (name, op) in all_functional_randvars
  eval(
  quote
  # Real
  function expand(X::$name, sym_to_var::SymbToVar, ctx::DReal.Context)
    ($op)(ctx, [expand(arg,sym_to_var,ctx) for arg in args(X)]...)
  end
  end)
end

# 1. If I'm a composite RandVar then expand all my children
# function expand(X::CompositeRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
#   ($op)(ctx, [expand(arg,sym_to_var,ctx) for arg in args(X)]...)
# end

# 2. If I'm an elementary randvar with constant arguments, do the interval trick
for Elem in subtypes(ElementaryRandVar)
  # Number of arguments
  nparams = num_params(Elem)

  @eval function expand{T}(X::$Elem{T, $([ConstantRandVar for i = 1:nparams])...}, sym_to_var::SymbToVar, ctx::DReal.Context)
    if haskey(sym_to_var, X)
      sym_to_var[X]
    else
      # Auxilary variable unbounded
      sym_to_var[X] = Var(ctx, T)
    end
  end

end

# 3. If I'm an elementary randvar with random parameters and closed fom quantile
#, then treat as (1) 
for Elem in subtypes(ClosedFormQuantileRandVar)
  # Number of arguments
  nparams = num_params(Elem)

  @eval function expand{T}(X::$Elem{T, $([SymbolicRandVar for i = 1:nparams])...}, sym_to_var::SymbToVar, ctx::DReal.Context)
    expand(quantile_expr(X), sym_to_var, ctx::DReal.Context)
  end
end

# 4. If I'm an elementary randvar with random parameters and no-closed form
# quantile then treat children as 1 and me as 2
for Elem in subtypes(ElementaryRandVar)
  # Number of arguments
  nparams = num_params(Elem)

  @eval function expand{T}(X::$Elem{T, $([SymbolicRandVar for i = 1:nparams])...}, sym_to_var::SymbToVar, ctx::DReal.Context)
    # expand(quantile_expr(X), sym_to_var, ctx::DReal.Context)
    if haskey(sym_to_var, X)
      sym_to_var[X]
    else
      # Auxilary variable unbounded
      sym_to_var[X] = Var(ctx, Float64, -Inf, Inf)
    end
  end
end

# 5. If Constant just return value
function expand(X::ConstantRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
  X.val
end

# 6. If Omega just return value
function expand(X::OmegaRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
  if haskey(sym_to_var, X)
    sym_to_var[X]
  else
    sym_to_var[X] = Var(ctx, Float64, "omega$(X.dim)", 0.0, 1.0)
  end
end


# function expand(X::NormalRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
#   if haskey(sym_to_var, X)
#     sym_to_var[X]
#   else
#     # Auxilary variable unbounded
#     sym_to_var[X] = Var(ctx, Float64, -Inf, Inf)
#   end
# end

# function expand(X::PoissonRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
#   if haskey(sym_to_var, X)
#     sym_to_var[X]
#   else
#     # Auxilary variable unbounded
#     # FIXME: use opensmt unbounded
#     sym_to_var[X] = Var(ctx, Int64)
#   end
# end

# # If it hss constant argument parents we can do this substituion
# # if not then do the expression
# function expand(X::UniformRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
#   if isa(X.lb, ConstantRandVar) && isa(X.ub, ConstantRandVar)
#     if haskey(sym_to_var, X)
#       sym_to_var[X]
#     else
#       sym_to_var[X] = Var(ctx, Float64)
#     end
#   else
#     expand((x.lb - x.ub)*omega_component(X.dim) + x.lb, sym_to_var, ctx::DRea.Context)
#   end
# end

## Calling DReal RandVars with input sets
## ======================================

function quantile{T<:Distribution}(::Type{T}, A::Interval, args...)
  dist = T(args...)
  quantile(dist, A)
end

"Returns lower and upper bounds for auxilary variable as function of event A"
function bounds(X::OmegaRandVar, A::AbstractOmega)
  A[X.dim]
end

"Returns lower and upper bounds for Normal RandVar as function of event A"
function bounds{T <: ElementaryRandVar}(X::T, args::Tuple, A::AbstractOmega)
  arg_bounds = [bounds(arg, A) for arg in args]
  quantile(distribution_type(T), A[X.dim], arg_bounds...)
end

"Returns lower and upper bounds for Normal RandVar as function of event A"
bounds(X::ConstantRandVar, A::AbstractOmega) = X.val

# FIXME: maybe lb and upper bound should be T but quantiles return Float and DReal has no mk_num for Ints

function add_bound_constraints!{T}(ctx::DReal.Context, X::DReal.Ex{T}, lb::Float64, ub::Float64)
  # DReal currently has trouble with infinities, so just dont add the contraint
  # Since we know it is unbounded anyway
  if lb != -Inf
    lb_constraint = (>=)(ctx, X, lb)
    DReal.add!(ctx, lb_constraint)
  end

  if ub != Inf
    ub_constraint = (<=)(ctx, X, ub)
    DReal.add!(ctx, ub_constraint)
  end
end

function is_sat(ex::Ex{Bool}, X::DRealRandVar{Bool}, A::AbstractOmega)
  ctx = X.ctx
  push_ctx!(ctx)
  # push!(debugstring, "(push 1)")

  ## Define subset (box) of Omega using assertions
  for (symb, var) in X.sym_to_var
    @show interval = bounds(symb, args(symb), A)
    add_bound_constraints!(ctx, var, interval.l, interval. u)
  end

  DReal.add!(ctx, ex)
  result = is_satisfiable(ctx)

  # push!(debugstring, "(pop 1)")
  pop_ctx!(ctx) #undo from 2 to here
  result
end

"""For a given event ``A`` finds X(A), i.e. are there points in a \in A
  such that X(A) is true, false or both"""
function call(X::DRealRandVar{Bool}, A::AbstractOmega)
  # 1. ∃ω ∈ A ∩ X : Does A contain any point X?
  # println("pos case")
  pos_case = is_sat(X.ex, X, A)

  # ∃ω ∈ A \ X : Does A contain any point not in X?
  # println("neg case2")
  notex = (!)(X.ctx, X.ex)
  neg_case = is_sat(notex, X, A)

  if pos_case & neg_case tf
  elseif pos_case t
  elseif neg_case f
  else
    # print(debugstring)
    error("Solver error: Query or its negation must be true")
  end
end
