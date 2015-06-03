# Pre-image Computation:
# ======================

for finame in ["tlmh.jl",
               "treelessmh.jl",
               "split.jl"]
    include(joinpath("refinement", finame))
end
