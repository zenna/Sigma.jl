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

(g::GaussianBump)(x, y) = gaussian(x, y, g.A, g.a, g.b, g.c, g.x0, g.y0)

## A Bump Solvable with a Linear Solver

immutable SquareBump <: Bump
  A
  x0
  y0
end

square(x, y, A, x0, y0) = ifelse((abs(x0 - x) < 0.5) &
                                  ((abs(y0 - y) < 0.5)),
                                  A,
                                  0.0)
(l::SquareBump)(x, y) = square(x, y, l.A, l.x0, l.y0)

immutable LinearBump <: Bump
  A
  x0
  y0
end

linear(x, y, A, x0, y0) = max(0.0,A*(1 - (abs(x0 - x) + abs(y0 - y))))
call(l::LinearBump, x, y) = linear(x, y, l.A, l.x0, l.y0)

@doc "Terrain" ->
abstract Terrain

@doc "Sum of Bumps" ->
immutable SumOfBumps <: Terrain
  bumps::Vector{Bump}
end

(t::SumOfBumps)(x, y) = sum([call(bump, x, y) for bump in t.bumps])

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
  @show "Computing integral_cost"
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

@doc "Generate a random path `path_length` long, starting at `start_pos`" ->
function gen_path_conditioned(start_pos, end_pos, path_length::Integer)
  path = Sigma.mvuniform(0.0, 3.0, 2, path_length)
  # First position in path is at start point
  path[:,1] =  start_pos

  # Then make path_length-1 moves
  path_constraints = Sigma.RandVar{Bool}[]
  for i = 1:path_length-1
    xdist = path[1,i] - path[1,i+1]
    ydist = path[2,i] - path[2,i+1]
    c = ((xdist == 0.0) & (ydist == 0.0)) | ((xdist == 1.0) & (ydist == 0.0)) |
      ((xdist == -1.0) & (ydist == 0.0)) | ((xdist == 0.0) & (ydist == 1.0)) |
      ((xdist == 0.0) & (ydist == -1.0))
    # c = xdist * xdist + ydist * ydist == 1.0
    push!(path_constraints,c)
  end
  hit_end = path[:,path_length] == end_pos
  # path, hit_end
  path, (&)(hit_end,path_constraints...)
end

@doc "Generate a random path `path_length` long, starting at `start_pos`" ->
function gen_path_discrete(start_pos, path_length::Integer)
  path = Sigma.RandArray(Float64, 2, path_length)
  # First position in path is at start point
  path[:,1] =  start_pos
  path[:,path_length] = end_pos

  # Then make path_length-1 moves
  for i = 2:path_length-1
    displacement = Sigma.uniform(0,1)
    move = ifelse(displacement > 0.8,
                 [0.0, 0.0],
           ifelse(displacement > 0.6,
                 [1.0, 0.0],
           ifelse(displacement > 0.4,
                 [-1.0, 0.0],
           ifelse(displacement > 0.2,
                 [0.0, 1.0],
                 [0.0, -1.0]))))
    path[:,i] = path[:,i-1] + move
  end
  path
end

@doc "Generate condition RandVar{Bool}, true iff observed path is optimal" ->
function optimal_cond(m::Terrain, observed::Path, start_pos::Pos, end_pos::Pos)
  # The cost of teh observed path is optimal
  optimal_cost = cost(observed, m)

  # In the sense that it is better than any path of length 2, 3, 4, ...
  alt_path_lengths = [2,4,6]
  optimal_conds = Sigma.RandArray(Bool,length(alt_path_lengths))

  # We will consider each case separately
  for i = 1:length(alt_path_lengths)
    # p, c = gen_path_conditioned(start_pos, end_pos, alt_path_lengths[i])
    # optimal_conds[i] =  (cost(p, m) >= optimal_cost) & c
    p = gen_path(start_pos, end_pos, alt_path_lengths[i])
    optimal_conds[i] =  (cost(p, m) >= optimal_cost)
  end
  # optimal_conds[1]
  (&)(optimal_conds...)
end


## Example
## =======
sigma_x = 1;
sigma_y = 2;
θ = pi/6
a = cos(θ)^2/2/sigma_x^2 + sin(θ)^2/2/sigma_y^2
b = -sin(2*θ)/4/sigma_x^2 + sin(2*θ)/4/sigma_y^2
c = sin(θ)^2/2/sigma_x^2 + cos(θ)^2/2/sigma_y^2

# # g = GaussianBump(1.0, a, b, c, 0.0, 0.0)
b1 = GaussianBump(1.0, a, b, c, Sigma.uniform(-2.5,2.5), Sigma.uniform(-2.5,2.5))
b2 = GaussianBump(1.0, a, b, c, Sigma.uniform(-2.5,2.5), Sigma.uniform(-2.5,2.5))
bumps = SumOfBumps([b1, b2])

# Goal
# start_pos = Sigma.RandArray([0.0, 0.0])
# end_pos = Sigma.RandArray([0.0, 2.0])

# # Example Terrain
# blue = Sigma.uniform(0,1)
# red = Sigma.uniform(0,1)
# bluered = Sigma.RandArray([blue,red])
# l1 = SquareBump(blue, 1.0, 0.0)
# l2 = SquareBump(blue, 1.0, 1.0)
# l3 = SquareBump(blue, 2.0, 1.0)
# l4 = SquareBump(red, 0.0, 1.0)
# bumps = SumOfBumps([l1,l2,l3,l4])

# m = [blue red blue
#      blue red blue
#      blue red blue
#      blue blue blue]

# function make_bumps(m)
#   bumps = Bump[]
#   for i = 1:size(m,1), j = 1:size(m,2)
#     push!(bumps, SquareBump(m[i,j], Float64(i) - 1.0, Float64(j) - 1.0))
#   end
#   bumps
# end

# bumps = SumOfBumps(make_bumps(m))


# # Example Path
# # p = [0.0 1.0 1.0 2.0 2.0
# #      0.0 0.0 1.0 1.0 0.0]

# p = [0.0 1.0 2.0 3.0 3.0 3.0 2.0 1.0 0.0
#      0.0 0.0 0.0 0.0 1.0 2.0 2.0 2.0 2.0]

# p = [0.0 0.0 0.0
#      0.0 1.0 2.0]

# # p = [0.0 0.0 0.0
# #      0.0 1.0 2.0]

# condition = optimal_cond(bumps, p, start_pos, end_pos)
# samples = rand(bluered, condition, 5; RandVarType = Sigma.Z3BinaryRandVar)


# function plot_mathematica(m, bluecost, redcost)
#   blues = []
#   reds = []
#   for i = 1:size(m,1), j = 1:size(m,2)
#     cost = m[i,j] === blue ? bluecost : redcost
#     cuboid = "Cuboid[{$(i-1), $(j-1), 0}, {$i, $j, $(Sigma.dofmt(cost))}]"
#     if m[i,j] === blue
#       push!(blues, cuboid)
#     else
#       push!(reds, cuboid)
#     end
#   end
#   blues, reds
# end

# function plot_errthing(blucues, redcues)
#   string("Graphics3D[{Green,Opacity[1.0],",
#     join(blucues, ",\n"),",\n",
#     "Red,Opacity[1.0],",w
#     join(redcues, ",\n"),
#     "}, ViewPoint -> {2.3, -1.4, 3.}]")
# end

# plots = []
# for sample in samples
#   bcost = sample[1]
#   rcost = sample[2]
#   bluemm, redmm = plot_mathematica(m, bcost, rcost)
#   push!(plots, plot_errthing(bluemm,redmm))
# end

# init_box = Sigma.unit_box(AbstractDomains.LazyBox{Float64}, Sigma.dims(condition))
# dreal_condition = convert(Sigma.DRealBinaryRandVar{Bool}, condition)
# Z3_condition = convert(Sigma.Z3BinaryRandVar{Bool}, condition)
# call(Z3_condition, init_box)


# pre_samples = Sigma.point_sample_mc(Z3_condition,1)

# l1s  = Sigma.call_type(l1,pre_samples[1])
# l2s  = Sigma.call_type(l2,pre_samples[1])
# bumpss = SumOfBumps([l1s, l2s])

# plot(layer(z=(x,y)->bumpss(x,y), x=linspace(-10,10,150), y=linspace(-10,10,150), Geom.contour),
#      layer(x=p[1,:], y=p[2,:], Geom.path))

# pre_tlmh(dreal_condition, init_box, 1)
# gaussian(x,y,A,a,b,c,x0,y0) = A*exp(-(a*(x-x0)^2 + 2b*(x-x0)*(y-y0)+c*(y-y0)^2))
# plot(z=(x,y)->gs(x,y), x=linspace(-100,100,150), y=linspace(-100,100,150), Geom.contour)

# call(l::LinearBump, x, y) = linear(x, y, l.A, l.x0, l.y0)
# l3 = LinearBump(3.0, -9.0, -9.3)

# plot(z=(x,y)->bumps(x,y), x=linspace(0,5,150), y=linspace(0,5,150), Geom.contour)

 # Any[0.021034784876292227,0.08543943377481596]
 # Any[0.0016419482937858677,0.07100088752947345]
 # Any[0.0634791269179561,0.22390229903715061]
 # Any[0.09033839983590489,0.500051715067946]
 # Any[0.09038618301775685,0.5000458410570601]
 # Any[0.09035668670744001,0.5000595796022183]
 # Any[0.09033818785247995,0.5000317375871334]
 # Any[0.09037238340826179,0.5000368246123037]
 # Any[0.09037027725727996,0.5000468258512568]
 # Any[0.04957249899351403,0.712245805959749]

# 10-element Array{Array{T,N},1}:
#  Any[0.40851795155801246,0.5036216270076627]
#  Any[0.17531285882917025,0.38015071523212934]
#  Any[0.8465487269703872,0.37803675314930363]
#  Any[0.6911817113247872,0.3577910062526371]
#  Any[0.1324974651141683,0.41389810303190827]
#  Any[0.6151574536636738,0.527793390970091]
#  Any[0.47748840631515943,0.6733902461861059]
#  Any[0.8142409503260998,0.6477525989560148]
#  Any[0.7710383703770307,0.36125520943716977]
#  Any[0.6979151983847683,0.031075791307149093]

# 5-element Array{Array{T,N},1}:
#  Any[5.4130838964013575e-5,0.4847191447838962]
#  Any[2.6995102535266175e-5,0.49810742642119366]
#  Any[5.130870877102897e-5,0.5709974893263304]
#  Any[5.368679145403241e-5,0.3926466421124112]
#  Any[4.306856174783945e-5,0.7753513345259593]
