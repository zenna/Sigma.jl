using Iterators
import Base.in
import Base.inv

abstract Box <: Real
ConcreteReal = Union(Float64,Int64)

type NDimBox <: Box
  intervals::Array{Float64,2}
end

ndcube(l::Float64, u::Float64, num_dims) = NDimBox(repmat([l,u],1,num_dims))

num_dims(b::NDimBox) = size(b.intervals,2)
volume(b::Box) = prod([b.intervals[2,i] - b.intervals[1,i] for i = 1:num_dims(b)])
logvolume(b::Box) = sum(map(log,[b.intervals[2,i] - b.intervals[1,i] for i = 1:num_dims(b)]))

## ==========
## Splitting
middle_point(i::Vector) = i[1] + (i[2] - i[1]) / 2
middle_point(b::Box) = [middle_point(b.intervals[:,i]) for i = 1:num_dims(b)]

split_box(i::Vector, split_point::Float64) = Array[[i[1],split_point],[split_point, i[2]]]

# Splits a box at a split-point along all its dimensions into n^d boxes
function split_box(b::Box, split_points::Vector{Float64})
  @assert(length(split_points) == num_dims(b))
  boxes = NDimBox[]
  splits = [split_box(b.intervals[:, i],split_points[i]) for i = 1:num_dims(b)]

  for subbox in apply(product, splits)
    z = Array(Float64,2,num_dims(b))
    for i = 1:size(z,2)
      z[:,i] = subbox[i]
    end
    push!(boxes, NDimBox(z))
  end
  boxes
end

# Split box into 2^d equally sized boxes by cutting down middle of each axis"
middle_split(b::Box) = split_box(b, middle_point(b))

function split_many_boxes{T}(to_split::Vector{T})
  bs = T[]
  for b in to_split
    for bj in middle_split(b)
      push!(bs, bj)
    end
  end
  bs
end

# ========
# Sampling

rand_interval(a::Float64, b::Float64) = a + (b - a) * rand()
rand(b::Box) = [apply(rand_interval,b.intervals[:,i]) for i = 1:num_dims(b)]
