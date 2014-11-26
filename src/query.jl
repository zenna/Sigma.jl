import Base: quantile, convert
import Distributions.pnormalize!

# =======
# Measure
# REVIEW: Remove move this to where it belongs, BOX, maybe delete it
measure{B<:Box}(bs::Vector{B}) = map(volume,bs)

for finame in ["bounds.jl",
               "samples.jl",]
    include(joinpath("query", finame))
end

## Convenience Aliases
## ==================
prob = prob_bfs
cond_prob = cond_prob_bfs
conditional = cond_bfs
cond_prob_sampled = cond_prob_bfs_sampled
rand(X::RandVar{Bool}, Y::RandVar{Bool}, nsamples::Int) = cond_sample_bfs(X,Y; nsamples = nsamples)
