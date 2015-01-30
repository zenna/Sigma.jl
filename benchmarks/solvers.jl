## Solvers
## =======

# Abstract Interpretation
immutable SigmaAI <: Algorithm
  capture::Vector{(Symbol, Type)}
  sampler::Function
  nproc::Int
  split::Function
end

immutable SigmaSMT <: Algorithm
  capture::Vector{(Symbol, Type)}
  solver::Sigma.SMTSolver
  sampler::Function
  nproc::Int
  split::Function
end
