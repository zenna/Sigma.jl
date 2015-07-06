# Construct a 2d polygon without any of its edges intersecting.
using Sigma

# function to_lines(points)
#   [line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
# end

typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  @show ppos
  @show qpos
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

function isintersectionfree(A::Mat)
  conditions = []

  # Iterate over all pairs of edges
  for i = 1:size(A,2)-1
    for j = i+1:size(A,2)-1
      ppos = A[:,i]
      pdir = A[:,i+1] - A[:,i]
      qpos = A[:,j]
      qdir = A[:,j+1] - A[:,j]
      s = intersect_segments(ppos,pdir, qpos, qdir)
      push!(conditions,(0 >= s) | (s >= 1))
    end
  end
  return (&)(conditions...)
end

Xs = mvuniform(0,0,1,2,20)
Y = isintersectionfree(Xs)
samples = rand(Xs,Y,1)
println(samples)
lines = to_lines(samples[1])
draw_lines(lines)
# draw_lines(to_lines(samples[1]))
