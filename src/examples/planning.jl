using Sigma
using Gadfly
# ========
# Examples

gen_path(n) = [uniform(j+5*(i-1), 0, 10) for i=1:2, j=1:n]

function point_in_box(x::Number,y::Number, box::Array{Float64, 2})
  (x >= box[1,1]) & (x <= box[2,1]) & (y >= box[1,2]) & (y <= box[2,2])
end

function point_in_box(x::Any,y::Any, box::Array{Float64, 2})
  (x >= box[1,1]) & (x <= box[2,1]) & (y >= box[1,2]) & (y <= box[2,2])
end

distance(a::Vector, b::Vector) = sqrt(sqr(b[1] - a[1]) + sqr(b[2] - a[2]))

function points_close(path::Array, min_step::Float64)
  distances_ok = true
  for i = 1:size(path,2) - 1
    j = i + 1
    distances_ok = distances_ok & (distance(path[:,i], path[:,j]) > min_step)
  end
  distances_ok
end

function not_in_obstacles(path, obstacles)
  no_collisions = true
  for i = 1:size(path,2)
    for obstacle in obstacles
      no_collisions = no_collisions & (!point_in_box(path[1,i], path[2,i], obstacle))
    end
  end
  no_collisions
end

# This function takes as input a path
# Assume as input I am only getting an
function valid_path(start_box, dest_box, obstacles, path_box)
  path = reshape(path_box,2,int(length(path_box)/2))
  svx, svy = path[:,1]
  good_start = point_in_box(svx,svy,start_box)

  dvx, dvy = path[:,end]
  good_dest = point_in_box(dvx,dvy,dest_box)

  good_distances = points_close(path, 5.0)

  avoids_obstacles  = not_in_obstacles(path,obstacles)

  good_start & good_dest & good_distances & avoids_obstacles
end

start_box = [1.01 1.01; 2.01 2.06]
dest_box = [5.01 5.02; 6.01 7.06]
obstacles = Array[[3.01 4.01; 4.01 5.56]]
path_box = gen_path(4)
v = valid_path(start_box,dest_box, obstacles, path_box)
d = cond_prob_deep(path_b$ox[2,2]>5, v, max_depth = 20)
d
println("whaa")
d
Sigma.measure(d[2])

## Vis

rand_take_n(v::Vector, n::Int) = [v[rand(1:length(v))] for i in 1:n]

function line_layer(b::Box)
  path_box  = rand(b)
  path = reshape(path_box,2,int(length(path_box)/2))
  layer(x=path[1,:], y=path[2,:], Geom.line)
end

function boxes_layer(bs::Vector{Box})
  x_min = Float64[]
  y_min = Float64[]
  x_max = Float64[]
  y_max = Float64[]

  for b in bs
    push!(x_min, b.intervals[1,1])
    push!(x_max, b.intervals[2,1])
    push!(y_min, b.intervals[1,2])
    push!(y_max, b.intervals[2,2])
  end

  layer(x_min=x_min, x_max=x_max, y_min=y_min,color=rand(length(bs)), y_max=y_max,Geom.rectbin)
end

# apply(plot, [boxes_layer([Box(start_box)]),
#              boxes_layer([Box(dest_box)]),
#              map(o->boxes_layer([Box(o)]),obstacles)...,
#              line_layer(preimage[rand(1:length(preimage))])])
