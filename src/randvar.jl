abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rand(X::RandVar) = call(X,SampleOmega())

rangetype(x) = typeof(x)

for finame in ["randvarsymbolic.jl",
               "randarray.jl",
               "conditionalrandvar.jl",]
    include(joinpath("randvar", finame))
end
