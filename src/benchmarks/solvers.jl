## Solvers
## =======

# Abstract Interpretation
immutable SigmaAI <: Algorithm
  capture::Vector{Symbol}
  sampler::Function
  ncores::Int
  split::Function
end

immutable SigmaSMT <: Algorithm
  capture::Vector{Symbol}
  solver::Sigma.SMTSolver
  sampler::Function
  ncores::Int
  split::Function
end

==(a::SigmaAI,b::SigmaAI) = equiv(a,b)
hash(a::SigmaAI, h::Uint) = deephash(a,h)
==(a::SigmaSMT,b::SigmaSMT) = equiv(a,b)
hash(a::SigmaSMT, h::Uint) = deephash(a,h)
