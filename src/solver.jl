@doc """Solvers inference problems.  Used mostly as an enumeration for different
  inference procedures, e.g. `rand(X,Y,DRealSolver)`""" ->
abstract Solver

immutable DRealSolver <: Solver end
immutable SigmaSolver <: Solver end