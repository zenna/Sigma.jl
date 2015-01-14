# using Sigma
using Compose
using Color

## Drawing
## =======
function make_point_pairs(lines)
  b = Array(Any, length(lines)-1)
  for i = 1:length(lines) - 1
    j = i + 1
    b[i] = [lines[i][:,1] lines[j][:,1]]
  end
  b
end

pair(x) = x[1],x[2]

function make_compose_lines(point_pairs)
  [line([pair(o[:,1]), pair(o[:,2])]) for o in point_pairs]
end

function draw_lines(lines...)
  all_lines = apply(vcat,lines)
  x = map(l->(context(units=UnitBox(0, 0, 1, 1)),
              l,
              linewidth(.5mm),
              stroke(rand_color()),
              fill(nothing)),
          all_lines)
  apply(compose,vcat(context(), x))
end

rand_color() = RGB(rand(),rand(),rand())

function to_lines(points)
  [line([pair(points[:,i]),pair(points[:,i+1])]) for i = 1:(size(points,2)-1)]
end

## Geometry
## ========
typealias Point Lifted{Vector{Float64}}
typealias Vec Lifted{Vector{Float64}}

# Where if anywhere, along p does it intersect segment
function intersect_segments(ppos::Point, pdir::Vec, qpos::Point, qdir::Vec)
  w = ppos - qpos
  u = pdir
  v = qdir
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
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

## Example
## =======

Xs = iid(Float64, i->uniform(i,0,1),2,10)
Y = isintersectionfree(Xs)
samples = cond_sample_mh(Xs,Y,0)
draw_lines(to_lines(samples[1]))
