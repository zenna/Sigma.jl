typealias Omega{T} Union(Vector{T},HyperBox{T}, LazyBox{T})
LazyOmega() = LazyBox(Float64)
LazyOmega{T<:Real}(T2::Type{T}) = LazyBox(T2)