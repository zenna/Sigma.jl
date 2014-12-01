using Iterators
import Base.in
import Base.inv

type HyperBox <: Domain{Float64}
  intervals::Array{Float64,2}
end

ndims(b::HyperBox) = size(b.intervals,2)

## Measure
## =======
measure(b::HyperBox) = prod([b.intervals[2,i] - b.intervals[1,i] for i = 1:ndims(b)])
measure{B<:HyperBox}(bs::Vector{B}) = [measure(b) for b in bs]
logmeasure(b::HyperBox) = sum(map(log,[b.intervals[2,i] - b.intervals[1,i] for i = 1:ndims(b)]))

## Splitting
## =========
mid{T<:Real}(i::Vector{T}) = i[1] + (i[2] - i[1]) / 2
mid(b::HyperBox) = Float64[mid(b.intervals[:,i]) for i = 1:ndims(b)]

# Splits a box at a split-point along all its dimensions into n^d boxes
function findproduct(splits::Vector{Vector{Vector{Float64}}}, b::HyperBox)
  boxes = HyperBox[]
  for subbox in apply(product, splits)
    z = Array(Float64,2,ndims(b))
    for i = 1:size(z,2)
      z[:,i] = subbox[i]
    end
    push!(boxes, HyperBox(z))
  end
  return boxes
end

function split_box(b::HyperBox, split_points::Vector{Float64})
  @assert(length(split_points) == ndims(b))
  boxes = HyperBox[]
  splits = [split_box(b.intervals[:, i],split_points[i]) for i = 1:ndims(b)]
  findproduct(splits, b)
end

# A partial split does not split along all dimensions
function partial_split_box(b::HyperBox, split_points::Dict{Int, Float64})
  @assert(length(keys(split_points)) <= ndims(b))

  boxes = HyperBox[]
  splits = Vector{Vector{Float64}}[]
  for i = 1:ndims(b)
    if haskey(split_points, i)
      push!(splits, split_box(b.intervals[:, i],split_points[i]))
    else # Don't split along this dimension
      push!(splits, Vector[b.intervals[:, i]])
    end
  end
  findproduct(splits, b)
end

# Split box into 2^d equally sized boxes by cutting down middle of each axis"
mid_split(b::HyperBox) = split_box(b, mid(b))

# Do a partial split at the midpoints of dimensiosns dims
mid_partial_split(b::HyperBox, dims::Vector{Int}) =
  partial_split_box(b,[i => mid(b.intervals[:,i]) for i in dims])

## Sampling
## ========
rand_interval(a::Float64, b::Float64) = a + (b - a) * rand()
rand(b::HyperBox) = [apply(rand_interval,b.intervals[:,i]) for i = 1:ndims(b)]
