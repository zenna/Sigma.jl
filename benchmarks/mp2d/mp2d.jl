``## Motion Planning 3D Benchmark
## =========================
using Sigma
using Lens
using Luxor
import Base.convert
# include("../vis.jl")

mappairs(f, v::Vector) = map(f, v[1:end-1], v[2:end])

# Use for functions which should take a normal or equivalently typed randarray
Point = AbstractVector
Vec = AbstractVector
Mat = AbstractMatrix

"A geometric entity of N dimensions"
abstract type Entity{N} end

"2D Rectangle"
immutable Rectangle <: Entity{2}
  bounds::Mat{Float64}
end

"Circle"
immutable Circle <: Entity{2}
  center::Vec{Float64}
  r
end

"Edge between defined by start and end points"
immutable Edge
  points::Mat
end

"Edge defined by origin and direction vector"
immutable ParametricEdge
  coords::Mat
end

function ParametricEdge(e::Edge)
  origin = e.points[:,1]
  dir = e.points[:,2] - e.points[:,1]
  ParametricEdge(hcat(origin,dir))
end

"Is the `point` in the `box`?"
function ispointinpoly(point::Point, box::Rectangle)
  r = (point[1] >= box.bounds[1,1]) &
      (point[1] <= box.bounds[2,1]) &
      (point[2] >= box.bounds[1,2]) &
      (point[2] <= box.bounds[2,2])
  r
end

"Where - if anywhere - along `p` does it intersect segment"
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  @show ppos
  @show qpos
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

"Do edges `e1` and `e2` not intersect?"
function intersects(e1::ParametricEdge, e2::ParametricEdge)
  s = intersect_segments(e1.coords[:,1], e1.coords[:,2],
                         e2.coords[:,1], e2.coords[:,2])
  (s < 0) | (s > 1)
end

"Forward kinematic function"
function kinematic(angles::Vector)
  total = angles[1]
  sin_total = sin(total)
  cos_total = cos(total)
  for i = 2:length(angles)
    total = total + angles[i]
    sin_total += sin(total)
    cos_total += cos(total)
  end
  sin_total, cos_total
end

"Compute vertices from angles"
function vertices(angles::Vector)
  xs = [0.0]
  ys = [0.0]
  total = 0.0
  sin_total = 0.0
  cos_total = 0.0
  for i = 1:length(angles)
    total = total + angles[i]
    sin_total += sin(total)
    xs = vcat(xs, [sin_total])
    cos_total += cos(total)
    ys = vcat(ys, [cos_total])
  end
  println(xs)
  println(ys)
  permutedims(hcat(xs, ys), (2, 1))
end

"Edge directions from points"
directions(points) = points[:, 2:end] - points[:, 1:end-1]

"Parametric Edges from angles"
function anglestoedge(angles::Vector)
  ps = vertices(angles)
  println("PS", ps)
  dirs = directions(ps)
  ps = ps[:, 1:end-1]
  @assert length(ps) == length(dirs)
  ps, dirs
  [ParametricEdge(hcat(ps[:, i], dirs[:, i])) for i = 1:size(ps, 2)]
end

"Does edge `e1` intersect with `circle`?"
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

intersects(e1::ParametricEdge, e2::Edge) = intersects(e1, ParametricEdge(e2))

"Do `points` avoid `obs`tacles?"
function pairwisecompare(edges::Vector, obs)
  conditions = [intersects(e, o) for e in edges, o in obs]
  (&)(conditions...)
end

function convert(::Type{Vector{ParametricEdge}}, points::RandArray)
  [ParametricEdge([points[:,i] (points[:,i+1] - points[:,i])])
           for i = 1:size(points,2)-1]
end

"Are `points` valid? starts at `origin`, ends at `dest`, avoids `obstacles`?"
function validpath(points, obstacles, origin, dest)
  is_start_ok = ispointinpoly(points[:, 1], origin)
  is_end_ok = ispointinpoly(points[:,end], dest)
  param_edges = convert(Vector{ParametricEdge}, points)
  avoids_obstacles = pairwisecompare(param_edges, obstacles)
  is_start_ok & avoids_obstacles & is_end_ok
end

function example_data(path_length::Integer)
  # obstacles = [Circle([5.0, 5.0], 3.0)]
  obstacles = [Circle([5.0, 5.0], 1.0)]
  points = mvuniform(0, 10, 2, path_length)
  origin = Rectangle([0.0 0.0
                      0.2 0.2])
  dest = Rectangle([9.9 9.9
                    10.0 10.0])
  points, origin, dest, obstacles
end

function test_mp2d(path_length = 4, nsamples = 1)
  points, origin, dest, obstacles = example_data(path_length)
  good_path = validpath(points, obstacles, origin, dest)
  sample = rand(points, good_path, nsamples; precision = 0.01, parallel = true, ncores = nprocs() - 1) / 10.0
end


function gettiming(results)
  timediffs2 = vcat([get(statsgo, proc_id=i, lensname=:sat_check) for i = 2:nprocs()]...)
  timediffs2 =  float(map(i->float(i)/1e9, timediffs2))
  mean(timediffs2), std(timediffs2)
end

"Draw the target at `x, y`"
function drawtarget(x, y)
  p1 = Luxor.Point(x, y)
  sethue("red")
  circle(p1, 0.1, :fill)
end

"Draw the path"
function drawpath(points)
  setline(3)
  curr = O
  for i = 1:size(points, 2)
    color = randomhue()
    sethue(color)
    x, y = points[1, i], points[2, i]
    println("XY", x, " ", y)
    point = Luxor.Point(x, y)
    line(curr, point, :stroke)
    curr = point
  end
end

function drawobstacles(obstacles)
  for ob in obstacles
    draw(ob)
  end
end

"Draw the path, target and obstacles"
function drawscene(points, obstacles, x, y)
  Drawing(1000, 1000, "scenes.png")
  origin()
  scale(50.0, 50.0)
  background("white")

  drawpath(points)
  drawobstacles(obstacles)
  drawtarget(x, y)

  finish()
  preview()
end


function run_benchmark()
  resultsgo, statsgo = capture(test_mp2d, [:distance, :sat_check, :post_loop])
end

"Draw a circle"
function draw(c::Circle)
  sethue("black")
  circle(Luxor.Point(c.center...), c.r, :fill)
end

function example_data_angles(path_length::Integer)
  angles = mvuniform(0.0, Float64(pi), path_length)
  obstacles = [Circle([0.5, 1.0], 0.2)]
  x_target = 2.4
  y_target = 1.5
  angles, obstacles, x_target, y_target
end

function test_angles(path_length = 4)
  angles, obstacles, x_target, y_target = example_data_angles(path_length)
  x, y = kinematic(angles)
  reach_condition = (x==x_target) & (y==y_target)

  param_edges = anglestoedge(angles)
  obstacle_condition = pairwisecompare(param_edges, obstacles)

  condition = reach_condition & obstacle_condition

  angles_sample = rand(angles, condition; precision=0.0001)
  angles_sample = angles_sample/Float64(pi) # Divide due to bug in DRealRandVar
  println("Actual Position", kinematic(angles_sample))
  points = vertices(angles_sample)
  print("Points", points)
  print("Angles", angles_sample)
  drawscene(points, obstacles, x_target, y_target)
end

test_angles()
