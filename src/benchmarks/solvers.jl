## Solvers
## =======

# Abstract Interpretation
immutable SigmaAI <: Algorithm
  capture::Vector{Symbol}
  sampler::Function
  nproc::Int
  split::Function
end

immutable SigmaSMT <: Algorithm
  capture::Vector{Symbol}
  solver::Sigma.SMTSolver
  sampler::Function
  nproc::Int
  split::Function
end
