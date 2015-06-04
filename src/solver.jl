@doc """Solvers inference problems.  Used mostly as an enumeration for different
  inference procedures, e.g. `rand(X,Y,DRealSolver)`""" ->
abstract Solver

abstract DReal <: Solver
immutable DRealSolver <: DReal end
immutable DRealSolverBinary <: DReal end

immutable SigmaSolver <: Solver end
immutable Z3SolverBianry <: Solver end