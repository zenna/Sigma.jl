## Motion Planning Benchmark
## =========================

# Construct a path from the start region to the target region
# which does not pass trhoug nay of the obstacles


typealias Point Lifted{Vector{Float64}}
typealias Vec Lifted{Vector{Float64}}
typealias Mat Lifted{Matrix{Float64}}
typealias PointPair Lifted{Matrix{Float64}}
typealias Edge Lifted{Matrix{Float64}}  #Parametric form of line is p1 + (p2 - p1)
typealias Scalar Lifted{Float64}

points_to_vec(p1::Point, p2::Point) = p1 - p2
points_to_vec(edge::PointPair) = points_to_vec(edge[:,1], edge[:,2])

# Parametric form of line is p1 + (p2 - p1)
points_to_parametric(p1::Point,p2::Point) = liftedarray([p1 points_to_vec(p2,p1)])
points_to_parametric(edge::PointPair) = points_to_parametric(edge[:,1], edge[:,2])
parametric_to_point(p::Edge, s::Scalar) = p[:,1] + s * p[:,2]

# Is the point in the box?
function ispointinpoly(point, box)
  r = (point[1] >= box[1,1]) &
    (point[1] <= box[2,1]) &
    (point[2] >= box[1,2]) &
    (point[2] <= box[2,2])
  r
end

# Linear Check
function avoid_obstacles(points, obs)
  observations = true
  for i = 1:size(points,2),ob in obs
    observations &= !point_in_poly(points[:,i],ob)
#     @show i, observations
  end
  observations
end

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

function short_lines(points, length::Float64)
  true
end

function isvalid_path(points, obstacles, origin, dest)
  point_in_poly(points[:,1],origin) &
  ispointinpoly(points[:,end], dest) &
  avoid_obstacles(points,obstacles) &
  short_lines(points, .1)
end

function linearplan(points)
  origin = [0.0 0.0
           0.2 0.2]
  dest = [.9 .9
          1.0 1.0]

  box1 = [.3  .1
          .65 .7]
  box2 = [.05 .7
          .25 .99]

  obstacles = Matrix[box1,box2]
  good_path = isvalid_path(points,obstacles,origin,dest)
  points,good_path
end


## Nonlinear
## =========
function isvalid_pathnl(points, obstacles, origin, dest)
  ispointinpoly(points[:,1],origin) &
  ispointinpoly(points[:,end], dest) &
  avoid_obstacles_nl(points,obstacles) &
  short_lines(points, .1)
end

# Nonlinear Check
function avoid_obstacles_nl(points, obs)
  observations = true
  for i = 1:size(points,2)-1, ob in obs
    p = points[:,i]
    pdir = points[:,i+1] - points[:,i]

    obpos = ob[:,1]
    obdir = ob[:,2]
    s = intersect_segments(p, pdir, obpos, obdir)
    observations &= (s < 0) | (s > 1)
  end
  observations
end

function nonlinearplan(points)
  origin = [0.0 0.0
           0.2 0.2]
  dest = [.9 .9
          1.0 1.0]
  obstacles = Array[[8.01 3.01; 1.02 9],
                    [0.5 3.08; 2.02 9.04],
                    [0.0 9.99; 3 5.04]]
  obs = map(points_to_parametric, obstacles)
  good_path = isvalid_pathnl(points,obs,origin,dest)
  points,good_path
end

points = mvuniform(0.0, 10.0, 2,6)
points, condition = nonlinearplan(points)
@show condition.smt
# s = cond_sample_tlmh(points,condition,1)

# # ## Draw
# obstacles = Array[[8.01 3.01; 1.02 9],
#                   [0.5 3.08; 2.02 9.04],
#                   [0.0 9.99; 3 5.04]]
# a = make_compose_lines(obstacles)
# points = s[1]
# b = [Compose.line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
# b
# draw_lines(a,b)
