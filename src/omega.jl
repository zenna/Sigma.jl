## Sample Space: Omega
## ==================

# Omega mathematically is defined as a unit n dimensional Euclidean hypercube.
# It is useful in different contexts to have types for
# 1. concrete elements ω in Omega - vectors or Real values
# 2. abstract values in Omega, which are subsets of Omega.
# 3. random values of Omega.
# Because we wan't to allow users to write moels without worrying about Omega,
# we use LazyBoxes to generate needed dimensions of Omega when required.

LazyOmega() = LazyBox(Float64)
LazyOmega{T<:Real}(T2::Type{T}) = LazyBox(T2)

@doc doc"""A Vector of whose values are sampled uniformly from [0,1], but are not
  created until accessed (hence Lazy).""" ->
immutable LazyRandomVector{T<:Real}
  samples::Dict{Int64,T}
end
LazyRandomVector{T<:Real}(T1::Type{T}) = LazyRandomVector(Dict{Int64,T1}())

function getindex{T}(o::LazyRandomVector{T}, key::Int)
  if haskey(o.samples,key)
    o.samples[key]
  else
    i = rand(T)
    o.samples[key] = i
    i
  end
end

function unit_box{T<:Real}(::Type{LazyBox{T}}, dims::Set{Int})
  @show "Getting UNIT BNOX"
  box = @show LazyBox(T)
  for dim in dims
    box[dim] = Interval{T}(zero(T), one(T))
  end
  box
end

@doc "All kinds of Omega" ->
typealias Omega{T} Union(Vector{T},HyperBox{T}, LazyBox{T}, LazyRandomVector{T}, Dict{Int,T})

@doc "Abstract representations of sample space - euclidean box" ->
typealias AbstractOmega{T} Union(HyperBox{T}, LazyBox{T})

@doc "A concrete (i.e. not abstract) element ω in sample space Ω" ->
typealias ConcreteOmega{T} Union(Vector{T}, LazyRandomVector{T})

@doc "Build an omega of `n` dimensions" ->
abstract_omega(n::Int) = HyperBox([Interval(0.0,1.0) for i = 1:n])