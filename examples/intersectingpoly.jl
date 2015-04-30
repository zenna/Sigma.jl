# Construct a 2d polygon without any of its edges intersecting.
using Sigma

function to_lines(points)
  [line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
end

function isintersectionfree(A::Lifted{Array{Float64,2}})
  condition = true

  # Iterate over all pairs of edges
  for i = 1:size(A,2)-1
    for j = i+1:size(A,2)-1
      ppos = A[:,i]
      pdir = A[:,i+1] - A[:,i]
      qpos = A[:,j]
      qdir = A[:,j+1] - A[:,j]
      s = intersect_segments(ppos,pdir, qpos, qdir)
#       @show i,j, s
      condition &= (0 >= s) | (s >= 1)
    end
  end
  return condition
end

Xs = mvuniformmeta(0,1,2,10)
Y = isintersectionfree(Xs)
samples = cond_sample_mh(Xs,Y,1)
# draw_lines(to_lines(samples[1]))