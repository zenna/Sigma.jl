## Motion Planning 3D Benchmark
## =========================

typealias Point Lifted{Vector{Float64}}
typealias Vec Lifted{Vector{Float64}}
typealias Mat Lifted{Matrix{Float64}}
# Use for functions which should take a normal or equivalently typed randarray

# A geometric entity of N dimensions
abstract Entity{N}

immutable Rectangle <: Entity{2}
  bounds::LA{Float64,2}
end

# ## Edges
# ## =====
# # Point Edge
immutable Edge
  points::LA{Float64,2}
end

immutable ParametricEdge
  coords::LA{Float64,2}
end

function parametric(e::Edge)
  origin = e.points[:,1]
  dir = e.points[:,2] - e.points[:,1]
  ParametricEdge(hcat(origin,dir))
end

# Is the point in the box?
function ispointinpoly(point, box::Rectangle)
  r = (point[1] >= box.bounds[1,1]) &
      (point[1] <= box.bounds[2,1]) &
      (point[2] >= box.bounds[1,2]) &
      (point[2] <= box.bounds[2,2])
  r
end

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
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
  ispointinpoly(points[:,1],origin) &
  ispointinpoly(points[:,end], dest) &
  avoid_obstacles(points,obstacles)
end

function test_mp2d()
  points = mvuniformmeta(0,10,2,4)
  origin = Rectangle([0.0 0.0
                      0.2 0.2])
  dest = Rectangle([.9 .9
                    1.0 1.0])
  obstacles = [Edge(ed) for ed in
               Array[[8.01 3.01; 1.02 9],
                     [0.5 3.08; 2.02 9.04],
                     [0.0 9.99; 3 5.04]]]
#   obs = map(points_to_parametric, obstacles)
  good_path = validpath(points,obstacles,origin,dest)
  points, good_path
end

## Test
## ====
model, condition = test_mp2d()
# cond_sample_tlmh(model,condition,1;solver=dreal3)

# @show model[1,1].smt
# o = Omega()
# @show condition.smt
# o
# call(condition,o)
# ndims(o)
# #

# a = Array[[8.01 3.01; 1.02 9],
#       [0.5 3.08; 2.02 9.04],
#       [0.0 9.99; 3 5.04]]

# e = Edge(a[1])
# b = parametric(e)

# b.coords[:,1]
# points = iidmeta(Float64,i->uniformmeta(i,0,10),2,4)
# points, condition = nonlinearplan(points)
# s = cond_sample_mh(points,condition,1)

# # ## Draw
# obstacles = Array[[8.01 3.01; 1.02 9],
#                   [0.5 3.08; 2.02 9.04],
#                   [0.0 9.99; 3 5.04]]
# a = make_compose_lines(obstacles)
# points = s[1]
# b = [Compose.line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
# b
# draw_lines(a,b)
