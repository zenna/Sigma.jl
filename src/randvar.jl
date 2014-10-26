abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

for finame in ["randvarsymbolic.jl",
               "randarray.jl",]
    include(joinpath("randvar", finame))
end
