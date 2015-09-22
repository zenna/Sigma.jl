## Implementation of MathProgBase interface for non-linear optimisation
## ====================================================================

import MathProgBase.SolverInterface: AbstractMathProgSolver, AbstractMathProgModel,
  getsense, numvar, numconstr, getobjval, getobjbound, getsolution, getsolvetime,
  setwarmstart!, loadnonlinearproblem!, optimize!, AbstractNLPEvaluator, status,
  obj_expr

## Solver Objects
## =============
export DRealSolver

immutable DRealSolver <: AbstractMathProgSolver
  precision::Float64
end

DRealSolver(;precision::Float64 = DEFAULT_PRECISION) = DRealSolver(precision)

type DRealMathProgModel <: AbstractMathProgModel
  ctx::Context
  status::Symbol
  numvar::Int
  vars::Vector{Ex}
  cost_var::Ex{Float64}
  constraint::Ex{Bool}
  sense::Symbol
  objbound::Interval
  solution::Vector{Interval}
  DRealMathProgModel(ctx::Context) = new(ctx, :Unsolved)
  DRealMathProgModel(ctx, numvar, vars, cost_var, constraint) =
    new(ctx, numvar, vars, cost_var, constraint)
end

function DRealMathProgModel(precision::Float64)
  warn("FIXME: using Global Context")
  # ctx = Context(qf_nra)
  ctx = global_context()
  set_precision!(ctx, precision)
  DRealMathProgModel(ctx)
end

MathProgBase.SolverInterface.model(s::DRealSolver) = DRealMathProgModel(s.precision)

## Interface Implementation
## ========================

getsense(m::DRealSolver) = m.sense
numvar(m::DRealSolver) = m.numvar
# numconstr(m::DRealSolver) = m.numconstr

# @doc "Best value" ->
getobjval(m::AbstractMathProgModel) = getobjbound(m).u

# @doc "Returns the best known bound on the optimal objective value" ->
function getobjbound(m::AbstractMathProgModel)
  m.status != :Optimal && error("Cannot get optimal value when status is $(m.status)")
  m.objbound
end

# @doc "Returns the solution vector found by the solver" ->
function getsolution(m::AbstractMathProgModel)
  m.status != :Optimal && error("Cannot get solution when status is $(m.status)")
  [mid(v) for v in m.solution]
end

# @doc "Returns the total elapsed solution time as reported by the solver." ->
# function getsolvetime(m::AbstractMathProgModel) end

# @doc "Provide an initial solution v to the solver, as supported." ->
function setwarmstart!(m::AbstractMathProgModel, v) end

# @doc "Loads the nonlinear programming problem into the model `m`." ->
function loadnonlinearproblem!(m::DRealMathProgModel,
                               numVar::Integer,
                               numConstr::Integer,
                               x_l::Vector{Float64},      # variable lower bounds
                               x_u::Vector{Float64},      # variable upper bounds
                               g_lb,     # constraint lower bounds
                               g_ub,     # constraint upper bounds
                               sense::Symbol, # :Max or :Min
                               d::AbstractNLPEvaluator)

  (sense == :Min || sense == :Max) || error("Unrecognized sense $sense")
  @assert length(x_l) == length(x_u) == numVar

  cost_var = Var(m.ctx, Float64, -100.00, 100.00)
  @show x_l
  @show x_u
  vars = [Var(m.ctx, Float64, x_l[i], x_u[i]) for i = 1:numVar]
  
  m.vars = vars
  @show obj_expr(d)
  # push_ctx!(m.ctx)
  add!(m.ctx, cost_var == eval(Expr(:let, obj_expr(d), :(x=$vars))))
  m.cost_var = cost_var
  m.sense = sense
  m.numvar = length(vars)
end

# @doc "Solves the optimization problem" ->
function optimize!(m::DRealMathProgModel)
  local cost
  local optimal_model
  try
    @show cost, optimal_model = minimize(m.ctx, m.cost_var, m.vars...; lb = -100.0, ub = 100.0)
  catch e
    reset_global_ctx!()
    rethrow(e)
  end
  m.status = :Optimal
  m.objbound = cost
  opt_sols_vec = Interval[optimal_model...]
  m.solution = opt_sols_vec
end

# @doc "Status after solving. Possible values include :Optimal, :Infeasible, :Unbounded, :UserLimit"
function status(m::DRealMathProgModel) m.status end