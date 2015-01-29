## Solvers
## =======

# Abstract Interpretation
immutable SigmaAI <: Algorithm
  capture::Vector{(Symbol, Type)}
  sampler::Function
  nproc::Int
  split::Function
end
