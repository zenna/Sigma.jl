abstract RandVar{T}

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rand(X::RandVar) = call(X,SampleOmega())
rand{T}(X::RandVar{T},nsamples::Int) = T[call(X,SampleOmega()) for i= 1:nsamples]

# default aliases
rand(X::RandVar,Y::RandVar{Bool};pre_args...) = cond_sample_bfs(X,Y;pre_args...)
rand(X::RandVar,Y::RandVar{Bool},nsamples::Int;pre_args...) = cond_sample_bfs(X,Y,nsamples;pre_args...)

rangetype{T<:RandVar}(::Type{T}) = T.parameters[1]
rangetype(x) = typeof(x) # Catch all (TODO: Why does this exist?)

for finame in ["randvarai.jl",
               "randvarsmt.jl",
               "randarray.jl",
               "randvarmeta.jl",]
    include(joinpath("randvar", finame))
end

## Convenience synonym
RandArray = PureRandArray
