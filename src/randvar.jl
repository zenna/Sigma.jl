abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rangetype(x) = typeof(x)

for finame in ["randvarsymbolic.jl",
               "randarray.jl",]
    include(joinpath("randvar", finame))
end
