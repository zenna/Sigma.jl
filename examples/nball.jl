# Sigma can be used to approximate the volume of an n-dimensional ball
using Sigma
using Base.Test

## Ground Truth
# unit n-sphere volume (n-ball surface area)
S(n) = n == 0 ? 2 : 2π*V(n-1)

# unit n-ball volume
V(n) = n == 0 ? 1 : S(n-1) / n

# ratio of n_ball volume to enclosing unit_sphere
ratio_V(n) = V(n) / 2^n

## Returns the probability that any x,y,z,.. within a unit
## n dim box will be within the enclosed sphere.
## Approximates volume of nball ground-truth
function unit_n_ball(num_dims::Integer)
  ncube = mvuniform(-1.0, 1.0, num_dims)
  sphere = sqrt(sum([x^2 for x in ncube])) < 1.0
  ncube, sphere
end

## Prob that point within n dim box will be element of smaller cube
## of side length 1 10th
function unit_n_box(lenratio::Float64, num_dims::Integer)
  @assert 0 < lenratio <= 1
  bigcube = mvuniform(-1.0, 1.0, num_dims)
  smallcube  = [(x > -lenratio) & (x < lenratio) for x in bigcube]
  smallcube_cond = apply(&, smallcube)
  bigcube, smallcube_cond
end

model, condition = unit_n_ball(10)
rand(model, condition)

model, condition = unit_n_box(0.5, 10)
rand(model, condition)
