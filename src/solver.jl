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