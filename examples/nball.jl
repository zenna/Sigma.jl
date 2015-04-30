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
  ncube = [uniform(i,-1.,1.) for i in 1:num_dims]
  sphere = sqrt(sum(map(sqr,ncube))) < 1
  ncube,sphere
end

## Prob that point within n dim box will be element of smaller cube
## of side length 1 10th
function unit_n_box(lenratio::Float64, num_dims::Integer)
  @assert 0 < lenratio <= 1
  bigcube = [uniform(i,-1.,1.) for i in 1:num_dims]
  smallcube  = map(x->(x>-lenratio) & (x < lenratio), bigcube)
  smallcube_cond = apply(&, smallcube)
  bigcube, smallcube_cond
end

for dimrange = 1:5
  bigcube, smallcube_cond = unit_n_box(lenratio,i)
  sampler = rand(bigcube[1], smallcube_cond)
end