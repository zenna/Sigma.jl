# using Sigma
# import Sigma: RandArray, uniform

typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix
typealias Path AbstractMatrix
typealias Pos AbstractVector

abstract Bump

@doc "2d Gaussian function" ->
function gaussian(x,y,A,a,b,c,x0,y0)
  xdiff = x-x0
  xdiff_sqr = xdiff*xdiff
  ydiff = y-y0
  ydiff_sqr = ydiff*ydiff
  A*exp(-(a*xdiff_sqr + 2b*xdiff*ydiff+c*ydiff_sqr))
end

immutable GaussianBump <: Bump
  A
  a
  b
  c
  x0
  y0
end

call(g::GaussianBump, x, y) = 
  gaussian(x, y, g.A, g.a, g.b, g.c, g.x0, g.y0)

## A Bump Solvable with a Linear Solver
linear(x, y, A, x0, y0) = max(0.0,A*(1 - (abs(x0 - x) + abs(y0 - y))))

immutable LinearBump <: Bump
  A
  x0
  y0
end

call(l::LinearBump, x, y) = linear(x, y, l.A, l.x0, l.y0)

@doc "Terrain" ->
abstract Terrain

@doc "Sum of Bumps" ->
immutable SumOfBumps <: Terrain
  bumps::Vector{Bump}
end

call(t::SumOfBumps, x, y) = sum([call(bump, x, y) for bump in t.bumps])

@doc "Compute cost of path on map `m`" -> 
function cost(p::Path, t::Terrain)
  path_length = size(p,2)
  point_costs = [call(t, p[1,i], p[2,i]) for i=1:path_length]
  sum(point_costs)
end

function cost_at_interpolate(p::Path, i::Integer, t::Terrain, displace::Float64)
  ax = p[1,i]
  ay = p[2,i]
  bx = p[1,i+1]
  by = p[2,i+1]
  call(t, ax + (bx - ax) * displace, ay + (by - ay) * displace)
end

@doc "Compute cost of path on map `m`" -> 
function integral_cost(p::Path, t::Terrain, samples_per_edge::Integer = 8)
  path_length = size(p,2)

  # Interpolat a segment at some number of points per edge
  # Treat first and last point separately
  displacements = collect(linspace(0,1,samples_per_edge))[2:end-1]
  
  point_costs = Any[]
  for i = 1:path_length-1
    # Add first point
    push!(point_costs, call(t, p[1,i], p[2,i]))
    
    for displace in displacements
      push!(point_costs, cost_at_interpolate(p, i, t, displace))
    end
  end
  sum(point_costs)
end

@doc "Generate a random path `path_length` long, starting at `start_pos`" -> 
function gen_path(start_pos, end_pos, path_length::Integer)
  path = Sigma.RandArray(Float64, 2, path_length)
  # First position in path is at start point
  path[:,1] =  start_pos
  path[:,path_length] = end_pos

  # Then make path_length-1 moves
  for i = 2:path_length-1
    path[:,i] = Sigma.mvuniform(-2.5,2.5,2,1)
  end
  path
end

@doc "Generate condition RandVar{Bool}, true iff observed path is optimal" -> 
function optimal_cond(m::Terrain, observed::Path, start_pos::Pos, end_pos::Pos)
  # The cost of teh observed path is optimal
  optimal_cost = integral_cost(observed, m)

  # In the sense that it is better than any path of length 2, 3, 4, ...
  alt_path_lengths = [2,3]
  optimal_conds = Sigma.RandArray(Bool,length(alt_path_lengths))

  # We will consider each case separately
  for i = 1:length(alt_path_lengths)
    p = gen_path(start_pos, end_pos, alt_path_lengths[i])
    optimal_conds[i] = (cost(p, m) >= optimal_cost)
  end
  # optimal_conds[1]
  (&)(optimal_conds...)
end

## Example
sigma_x = 1;
sigma_y = 2;
θ = pi/6
a = cos(θ)^2/2/sigma_x^2 + sin(θ)^2/2/sigma_y^2
b = -sin(2*θ)/4/sigma_x^2 + sin(2*θ)/4/sigma_y^2
c = sin(θ)^2/2/sigma_x^2 + cos(θ)^2/2/sigma_y^2

g = GaussianBump(1.0, a, b, c, 0.0, 0.0)
bumps = SumOfBumps([GaussianBump(1.0, a, b, c, Sigma.uniform(-2.5,2.5), Sigma.uniform(-2.5,2.5)) for i = 1:2])
# gs = SumOfBumps([GaussianBump(1.0, a+rand(Sigma.uniform(0,1)), b+rand(Sigma.uniform(0,1)), c+rand(Sigma.uniform(0,1)), rand(Sigma.uniform(-2.5,2.5)), rand(Sigma.uniform(-2.5,2.5))) for i = 1:6])

l1 = LinearBump(2.0, Sigma.uniform(-5.0,5.0), Sigma.uniform(-5.0,5.0))
l2 = LinearBump(4.0, Sigma.uniform(-5.0,5.0), Sigma.uniform(-5.0,5.0))
bumps = SumOfBumps([l1,l2])

# Example Path
p = [-3.0 -0.1 2.0
     -3.4 0.0  0.0]

start_pos = Sigma.RandArray([-3.0, -3.4])
end_pos = Sigma.RandArray([2.0, 0.0])

condition = optimal_cond(bumps, p, start_pos, end_pos)

init_box = Sigma.unit_box(AbstractDomains.LazyBox{Float64}, Sigma.dims(condition))
dreal_condition = convert(Sigma.DRealBinaryRandVar{Bool}, condition)
Z3_condition = convert(Sigma.Z3BinaryRandVar{Bool}, condition)
# # println("Calling")
call(Z3_condition, init_box)

pre_samples = Sigma.point_sample_mc(Z3_condition,1)

l1s  = Sigma.call_type(l1,pre_samples[1])
l2s  = Sigma.call_type(l2,pre_samples[1])
bumpss = SumOfBumps([l1s, l2s])
plot(layer(z=(x,y)->bumpss(x,y), x=linspace(-10,10,150), y=linspace(-10,10,150), Geom.contour),
     layer(x=p[1,:], y=p[2,:], Geom.path))

# pre_tlmh(dreal_condition, init_box, 1)
# gaussian(x,y,A,a,b,c,x0,y0) = A*exp(-(a*(x-x0)^2 + 2b*(x-x0)*(y-y0)+c*(y-y0)^2))
# plot(z=(x,y)->gs(x,y), x=linspace(-100,100,150), y=linspace(-100,100,150), Geom.contour)

# call(l::LinearBump, x, y) = linear(x, y, l.A, l.x0, l.y0)
# l3 = LinearBump(3.0, -9.0, -9.3)

# plot(z=(x,y)->l(x,y), x=linspace(-10,10,150), y=linspace(-10,10,150), Geom.contour)
