abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rand(X::RandVar) = call(X,SampleOmega())
rand{T}(X::RandVar{T},nsamples::Int) = T[call(X,SampleOmega()) for i= 1:nsamples]

# default aliases
rand(X::RandVar,Y::RandVar{Bool}) = cond_sample_bfs(X,Y)
rand(X::RandVar,Y::RandVar{Bool},nsamples::Int) = cond_sample_bfs(X,Y,nsamples)

# Catch all
rangetype(x) = typeof(x)


for finame in ["randvarsymbolic.jl",
               "randarray.jl",
               "conditionalrandvar.jl",]
    include(joinpath("randvar", finame))
end

## Convenience synonym
RandArray = PureRandArray
