## Abstract Markov Chain
## =====================

AbstractChain{T<:Domain} = Vector{T}

"Get point samples out of a abstract Markov chain"
point_sample(chain::AbstractChain) = [rand(state) for state in chain]
