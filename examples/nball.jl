# See how preimage refinement scales with increasing d
using Sigma
using Gadfly
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

# There are two ways to formulate this problem
# The first is to say you have a set of unit random variables
# And you want to know the probability that an element is within the enclosing ball
function prob_error(dimrange::Range)
  ncube, sphere = unit_n_ball(8)
  ground = [ratio_V(i) for i = dimrange]
  errors = [unit_n_ball(i) for i = dimrange]
  plot(x=dimrange, y=ground, ymin=map(x->x[1],errors),
       ymax=map(x->x[2],errors), Geom.point, Geom.errorbar)
end

# The second way is to say you want to sample from a random variable conditioned
# on it being within the unit sphere
function nbox_sampler_error(dimrange::Range, lenratio::Float64; nsamples = 50000)
  plots = Plot[]
  for i in dimrange
    bigcube, smallcube_cond = unit_n_box(lenratio,i)
    sampler = cond_sample(bigcube[1], smallcube_cond)
    samples = [sampler(1000) for i = 1:nsamples]
    push!(plots, plot(x = map(x->x[2],samples), Geom.histogram))
  end
  plots
end


# The second way is to say you want to sample from a random variable conditioned
# on it being within the unit sphere
function nball_sampler_error(dimrange::Range; nsamples = 50000)
  plots = Plot[]
  for i in dimrange
    ncube, sphere = unit_n_ball(i)
    sampler = cond_sample(ncube[1], sphere)
    samples = [sampler(1000) for i = 1:nsamples]
    push!(plots, plot(x = map(x->x[2],samples), Geom.histogram))
  end
  plots
end

# Draw
boxplots = nbox_sampler_error(3:5,.1)

sample_plots = nball_sampler_error(3:8)
