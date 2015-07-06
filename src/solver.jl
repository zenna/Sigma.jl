@doc """Solvers inference problems.  Used mostly as an enumeration for different
  inference procedures, e.g. `rand(X,Y,DRealSolver)`""" ->
abstract Solver

abstract DReal <: Solver
immutable DRealSolver <: DReal end
immutable DRealSolverBinary <: DReal end

immutable SigmaSolver <: Solver end
immutable Z3SolverBianry <: Solver end

DREAL_SOLVER_ON && include(joinpath("solver","dreal.jl"))
SIGMA_SOLVER_ON && include(joinpath("solver","sigma.jl"))
DREAL_BINARY_SOLVER_ON && include(joinpath("solver","drealbinary.jl"))

include(joinpath("solver","z3binary.jl"))

# Set the default rrand var
global global_randvar = DRealBinaryRandVar
default_randvar() = (global global_randvar; global_randvar)
function set_default_randvar!{T<:RandVar}(R::Type{T})
  println("Setting default solver to $R")
  global global_randvar
  global_randvar = T
end