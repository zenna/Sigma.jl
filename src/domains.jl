## Functions for abstract domains from AbstractDomains.jl for inference
## ====================================================================

for finame in ["interval.jl"]
    include(joinpath("domains", finame))
end
