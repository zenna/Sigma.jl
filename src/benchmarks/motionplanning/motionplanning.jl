using Compose
using Color

function point_in_poly(point, box)
  r = (point[1] >= box[1,1]) &
    (point[1] <= box[2,1]) &
    (point[2] >= box[1,2]) &
    (point[2] <= box[2,2])
#   @show point[1], box[1,1]
  r
end

function avoid_obstacles(points, obs)
  observations = true
  for i = 1:size(points,2),ob in obs
    observations &= !point_in_poly(points[:,i],ob)
#     @show i, observations
  end
  observations
end

function short_lines(points, length::Float64)
  true
end

function isvalid_path(points, obstacles, origin, dest)
  point_in_poly(points[:,1],origin) &
    point_in_poly(points[:,end], dest) &
    avoid_obstacles(points,obstacles) &
    short_lines(points, .1)
end

## Example
## =======
points = iid(Float64,i->uniform(i,0,1),2,10)
origin = [0.0 0.0
         0.2 0.2]
dest = [.9 .9
        1.0 1.0]

box1 = [.3  .1
        .65 .7]
box2 = [.05 .7
        .25 .99]

obstacles = Matrix[box1,box2]
points = iid(Float64,i->uniform(i,0,1),2,3)
good_path = isvalid_path(points,obstacles,origin,dest)
samples = rand(points, good_path,10)

## Vis
## ===
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
  x = map(l->(context(units=UnitHyperBox(0, 0, 10, 10)),
              l,
              linewidth(.5mm),
              stroke(rand_color()),
              fill(nothing)),
          all_lines)
  apply(compose,vcat(context(), x))
end

rand_color() = RGB(rand(),rand(),rand())
