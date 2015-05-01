## Geometry Utils
## ===============

# Types and functions useful for geometric benchmarks

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

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

function normalise(v::Vec)
  denom = sqrt(sqr(v[1]) + sqr(v[2]))
  liftedarray([v[i] / denom for i = 1:length(v)])
end