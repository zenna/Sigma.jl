import Base: quantile, convert
import Distributions.pnormalize!

for finame in ["bounds.jl",
               "samples.jl",]
    include(joinpath("query", finame))
end
