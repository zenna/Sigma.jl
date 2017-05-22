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

function set_precision!(Y::DRealRandVar, precision::Float64)
  println("Setting DReal RandVar precision to $precision")
  DReal.set_precision!(Y.ctx, precision)
end

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
    rvargs = [expand(arg,sym_to_var,ctx) for arg in args(X)]
    ($op)(ctx, rvargs...)
  end
  end)
end

# ## Ambiguity
# function expand(X::ClosedFormQuantileRandVar, sym_to_var::SymbToVar, ctx::DReal.Context, args::ConstantRandVar...)
#   expr = quantile_expr(X)
#   expand(expr, sym_to_var, ctx::DReal.Context, args(expr)...)
# end

# 3. If I'm an elementary randvar with random parameters and closed fom quantile
function expand{T}(X::ClosedFormQuantileRandVar{T}, sym_to_var::SymbToVar, ctx::DReal.Context)
  # If all args are constant do the interval trick
  if all([isa(arg, ConstantRandVar) for arg in args(X)])
    if haskey(sym_to_var, X)
      sym_to_var[X]
    else
      # Auxilary variable unbounded
      sym_to_var[X] = Var(ctx, T)
    end
  # Otherwise expand it symbolically
  else
    expand(quantile_expr(X), sym_to_var, ctx::DReal.Context)
  end
end

# # 2. If not closedform elementary randvar , do the interval trick
# if arguments not constant then we'll get error at bound stage
function expand{T}(X::ElementaryRandVar{T}, sym_to_var::SymbToVar, ctx::DReal.Context)
  if haskey(sym_to_var, X)
    sym_to_var[X]
  else
    # Auxilary variable unbounded
    sym_to_var[X] = Var(ctx, T)
  end
end

# 5. If Constant just return value
expand(X::ConstantRandVar, sym_to_var::SymbToVar, ctx::DReal.Context) = X.val

# 6. If Omega just return value
function expand(X::OmegaRandVar, sym_to_var::SymbToVar, ctx::DReal.Context)
  if haskey(sym_to_var, X)
    sym_to_var[X]
  else
    sym_to_var[X] = Var(ctx, Float64, "omega$(X.dim)", 0.0, 1.0)
  end
end

## Calling DReal RandVars with input sets
## ======================================

# FIXME: A should be an interval or a real, need a type for this, or do i
function quantile{T<:Distribution}(::Type{T}, A, args...)
  dist = T(args...)
  quantile(dist, A)
end

"Returns lower and upper bounds for auxilary variable as function of event A"
function bounds(X::OmegaRandVar, A::AbstractOmega)
  A[X.dim]
end

"Returns lower and upper bounds for Elementary RandVar as function of event A"
function bounds{T <: ElementaryRandVar}(X::T, A::AbstractOmega)
  arg_bounds = [bounds(arg, A) for arg in args(X)]
  quantile(distribution_type(T), A[X.dim], arg_bounds...)
end

"Returns lower and upper bounds for Constant RandVar as function of event A"
bounds(X::ConstantRandVar, A::AbstractOmega) = X.val

# FIXME: maybe lb and upper bound should be T but quantiles return Float and DReal has no mk_num for Ints
function add_bound_constraints!{T}(ctx::DReal.Context, X::DReal.Ex{T}, lb::Float64, ub::Float64)
  # DReal currently has trouble with infinities, so just dont add the contraint
  # Since we know it is unbounded anyway
  if lb != -Inf
    lb_constraint = (>=)(ctx, X, lb)
    DReal.add!(ctx, lb_constraint)
    # println("lb_constraint = (>=)(ctx, X, $lb)")
    # println("DReal.add!(ctx, lb_constraint)")
  end

  if ub != Inf
    ub_constraint = (<=)(ctx, X, ub)
    DReal.add!(ctx, ub_constraint)
    # println("ub_constraint = (<=)(ctx, X, $ub)")
    # println("DReal.add!(ctx, ub_constraint)")
  end
end

function is_sat(ex::Ex{Bool}, X::DRealRandVar{Bool}, A::AbstractOmega)
  # println("Testing issat")
  ctx = X.ctx
  push_ctx!(ctx)
  # println("push_ctx!(ctx)")
  # push!(debugstring, "(push 1)")

  ## Define subset (box) of Omega using assertions
  ## For each variable - add constraints on its lower and upper bounds
  for (symb, vari) in X.sym_to_var
    interval = bounds(symb, A)
    add_bound_constraints!(ctx, vari, interval.l, interval. u)
  end

  DReal.add!(ctx, ex)
  # println("DReal.add!(ctx, ex)")
  result = is_satisfiable(ctx)
  # println("result = is_satisfiable(ctx)")

  # push!(debugstring, "(pop 1)")
  pop_ctx!(ctx) #undo from 2 to here
  # println("pop_ctx!(ctx)")
  result
end

"""For a given event ``A`` finds X(A), i.e. are there points in a \in A
  such that X(A) is true, false or both"""
function (X::DRealRandVar{Bool})(A::AbstractOmega)
  # 1. ∃ω ∈ A ∩ X : Does A contain any point X?
  # println("pos case")
  pos_case = is_sat(X.ex, X, A)

  # ∃ω ∈ A \ X : Does A contain any point not in X?
  # println("neg case2")
  notex = (!)(X.ctx, X.ex)
  # FIXME: Store this Not Ex
  # println("ex = (!)(X.ctx, ex)")
  neg_case = is_sat(notex, X, A)
  # println("Tested both cases: $pos_case $neg_case")

  if pos_case & neg_case tf
  elseif pos_case t
  elseif neg_case f
  else
    # print(debugstring)
    error("Solver error: Query or its negation must be true")
  end
end


"Returns some subet A ⊆ init_box s.t. Y(A) == true.  Also returns probability it sampled that box"
function preimage_proposal{D <: Domain}(Y::DRealRandVar{Bool}, init_box::D; args...)
  DReal.push_ctx!(Y.ctx)

  ## Define subset (box) of Omega using assertions
  for (symb, vari) in Y.sym_to_var
    interval = bounds(symb, init_box)
    add_bound_constraints!(Y.ctx, vari, interval.l, interval. u)
  end
  DReal.add!(Y.ctx, Y.ex)

  issat = DReal.is_satisfiable()

  !issat && error("Cannot condition on unsatisfiable events")

  A = LazyBox(Float64) #FIXME Float64 too speific?
  for (symb, var) in Y.sym_to_var
    A[symb.dim] = DReal.model(Y.ctx, var)
  end

  # I believe all the boxes are going to have the same size, so assuming that's true
  # we can just return some constant for the size.

  # As for the box itself, we need to return an abstract omega.
  dummy_ex = first(Y.sym_to_var)[2]
  logq = 0.5
  # logq = DReal.opensmt_get_model_logprob(Y.ctx.ctx, dummy_ex.e)
  DReal.pop_ctx!(Y.ctx)
  A, logq, 1.0
end

cleanup(Y::DRealRandVar) = DReal.delete_ctx!(Y.ctx)
