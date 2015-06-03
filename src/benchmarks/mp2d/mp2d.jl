## Motion Planning 3D Benchmark
## =========================
# using Sigma

typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix
# Use for functions which should take a normal or equivalently typed randarray

# A geometric entity of N dimensions
abstract Entity{N}

immutable Rectangle <: Entity{2}
  bounds::Mat{Float64}
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

function intersects(e1::ParametricEdge, e2::ParametricEdge)
  s = intersect_segments(e1.coords[:,1], e1.coords[:,2],
                         e2.coords[:,1], e2.coords[:,2])
  (s < 0) | (s > 1)
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

function test_mp2d(path_length::Integer)
  points = mvuniform(-1,0,10,2,path_length*2)
  origin = Rectangle([0.0 0.0
                      0.2 0.2])
  dest = Rectangle([9.9 9.9
                    10.0 10.0])
  obstacles = [Edge(ed) for ed in
               Array[[8.01 3.01; 1.02 9],
                     [0.5 3.08; 2.02 9.04],
                     [0.0 9.99; 3 5.04]]]
#   obs = map(points_to_parametric, obstacles)
  good_path = validpath(points,obstacles,origin,dest)
  points, good_path
end

# ## Test
# ## ====
model, condition = test_mp2d(4)
# Sigma.dims(condition)

# a = Sigma.build_init_box(condition,Set{IBEX.ExprSymbol}())
# using Cxx
abstract_samples  = Sigma.pre_tlmh(condition,1)
print(abstract_samples[])

# a = abstract_samples[1]
# rand(a)
# call(model[1,1],rand(a))
# sample = rand(model,condition,1)
# Sigma.dims(condition)
# origin = Rectangle([0.0 0.0
#                     0.2 0.2])
# dest = Rectangle([.9 .9
#                   1.0 1.0])
# obstacles = [Edge(ed) for ed in
#              Array[[8.01 3.01; 1.02 9],
#                    [0.5 3.08; 2.02 9.04],
#                    [0.0 9.99; 3 5.04]]]
# validpath(points, obstacles, origin, dest)
# ## Draw

include("../vis.jl")
function drawthething(sample)
  obstacles = Array[[8.01 3.01; 1.02 9],
                    [0.5 3.08; 2.02 9.04],
                    [0.0 9.99; 3 5.04]]
  lines = make_compose_lines(obstacles)

  points = call(model, rand(sample))
  b = [Compose.line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
  draw_lines(b,lines)
end

drawthething(abstract_samples[1])
