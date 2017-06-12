## Motion Planning 3D Benchmark
## =========================
using Sigma
using Lens
include("../vis.jl")

# Use for functions which should take a normal or equivalently typed randarray
typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix

# A geometric entity of N dimensions
abstract Entity{N}

immutable Rectangle <: Entity{2}
  bounds::Mat{Float64}
end

immutable Circle <: Entity{2}
  center::Vec{Float64}
  r
end

# ## Edges
# ## =====
# # Point Edge
immutable Edge
  points::Mat
end

immutable ParametricEdge
  coords::Mat
end

function parametric(e::Edge)
  origin = e.points[:,1]
  dir = e.points[:,2] - e.points[:,1]
  ParametricEdge(hcat(origin,dir))
end

# Is the point in the box?
function ispointinpoly(point::Point, box::Rectangle)
  r = (point[1] >= box.bounds[1,1]) &
      (point[1] <= box.bounds[2,1]) &
      (point[2] >= box.bounds[1,2]) &
      (point[2] <= box.bounds[2,2])
  r
end

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  @show ppos
  @show qpos
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

# Does not intersect
function intersects(e1::ParametricEdge, e2::ParametricEdge)
  s = intersect_segments(e1.coords[:,1], e1.coords[:,2],
                         e2.coords[:,1], e2.coords[:,2])
  (s < 0) | (s > 1)
end

function intersects(e1::ParametricEdge, circle::Circle)
  rayorig = e1.coords[:,1]
  raydir = e1.coords[:,2]
  r = circle.r
  f = rayorig - circle.center # Vector from center sphere to ray start
  a = dot(raydir, raydir)
  b = 2.0 * dot(f,raydir)
  c = dot(f,f) - r*r

  # discriminant
  b*b-4*a*c < 0
end

intersects(e1::ParametricEdge, e2::Edge) = intersects(e1, parametric(e2))

function pairwisecompare(edges::Vector, obs)
  conditions = [intersects(e,o) for e in edges, o in obs]
  (&)(conditions...)
end

# Nonlinear Check
function avoid_obstacles(points, obs)
  # Convert poitns into edges and check whether all
  # edges miss all obstacles
  edges = [ParametricEdge([points[:,i] (points[:,i+1] - points[:,i])])
           for i = 1:size(points,2)-1]
  pairwisecompare(edges, obs)
end

function validpath(points, obstacles, origin, dest)
  ispointinpoly(points[:,1],origin) & ispointinpoly(points[:,end], dest) & avoid_obstacles(points,obstacles)
end

function test_mp2d(obstacles, path_length::Integer)
  points = mvuniform(0,10,2, path_length)
  origin = Rectangle([0.0 0.0
                      0.2 0.2])
  dest = Rectangle([9.9 9.9
                    10.0 10.0])
  # obstacles = [Circle([5.0, 5.0], 3.0)]
  # obstacles = [Edge(ed) for ed in
  #              Array[[8.01 3.01; 1.02 9],
  #                    [0.5 3.08; 2.02 9.04],
  #                    [0.0 9.99; 3 5.04]]]
  #   obs = map(points_to_parametric, obstacles)
  good_path = validpath(points, obstacles, origin, dest)
  points, good_path
end

# ## Test
# ## ====
function mpgo()
  obstacles = [Circle([5.0, 5.0], 3.0), Circle([4.0, 8.0], 5)]
  model, condition = test_mp2d(obstacles, 6)
  sample = rand(model, condition, 100; precision = 0.01, parallel = true, ncores = nprocs() - 1) / 10.0
end

# sample = [1.64807   1.8789  74.3919  65.4604  99.5862  55.8671  99.3301  99.2311
#           1.24775  10.3224  33.2845  49.7916  88.6606  26.1991  98.028   99.5821]

function gettiming(results)
  timediffs2 = vcat([get(statsgo, proc_id=i, lensname=:sat_check) for i = 2:nprocs()]...)
  timediffs2 =  float(map(i->float(i)/1e9, timediffs2))
  mean(timediffs2), std(timediffs2)
end


function gencompose(c::Circle)
  (context(units=UnitBox(0, 0, 10, 10)),
   Compose.circle(c.center[1], c.center[2], c.r),
   linewidth(.5mm),
   stroke(Compose.RGB(rand(),rand(),rand())),
   fill(nothing))
end

function drawthething(points, obstacles)
  # obstacles = Array[[8.01 3.01; 1.02 9],
  #                   [0.5 3.08; 2.02 9.04],
  #                   [0.0 9.99; 3 5.04]]
  # lines = make_compose_lines(obstacles)

  b = [Compose.line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
  @show c_lines = get_lines(b)
  @show c_obstacles = map(gencompose, obstacles)
  @show all_items = vcat(c_lines, c_obstacles)#Any[c_lines..., c_obstacles...]

  apply(compose, vcat(context(), all_items))
  # draw_lines(b,lines)
end

function main()
  println("Running Main")
  op = drawthething(sample, obstacles)
  img = SVG("path.svg", 4inch, 4(sqrt(3)/2)inch)
  draw(img, op)
  # ## Draw
end

function run_benchmark()
  resultsgo, statsgo = capture(mpgo, [:distance, :sat_check, :post_loop])
end

mpgo()
