typealias Lifted{T} Union(T, Domain{T}, RandVar{T})

# Use for functions which should take a normal or equivalently typed randarray
typealias LiftedArray{T,N} Union(Array{T,N}, RandArray{T,N})

# Defaults to identity function on normal array
# But when input array contains random variables, we convert it into a RandArray
liftedarray{T<:Any}(Xs::Array{T}) = Xs
liftedarray{T<:RandVar, N}(Xs::Array{T,N}) = PureRandArray{eltype(Xs).parameters[1],N}(Xs)
Callable = Union(RandVar, Function, DataType)
