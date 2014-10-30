abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rand(X::RandVar) = call(X,SampleOmega())
rand{T}(X::RandVar{T},nsamples::Int64) = T[call(X,SampleOmega()) for i= 1:nsamples]

rangetype(x) = typeof(x)

for finame in ["randvarsymbolic.jl",
               "randarray.jl",
               "conditionalrandvar.jl",]
    include(joinpath("randvar", finame))
end
