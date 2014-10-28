# Pool like simulation/inference
using Sigma
using Compose
using Color

## Conversion
## ==========

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
function intersect_segments(p::Edge, q::Edge)
  w = p[:,1] - q[:,1]
  u = p[:,2]
  v = q[:,2]
  (v[2] * w[1] - v[1] * w[2]) / (v[1] * u[2] - v[2] * u[1])
end

perp(v::Vec) = liftedarray([-v[2],v[1]])
function normalise(v::Vec)
  denom = sqrt(sqr(v[1]) + sqr(v[2]))
  liftedarray([v[i] / denom for i = 1:length(v)])
end

function reflect(v::Vec,q::Vec)
  q_norm = normalise(q)
  n_amb = perp(q_norm)
  v2 = normalise(v)
  n = @If dot(q_norm,v2) < 0 n_amb -n_amb
  v2 - 2 * (dot(v2,n) * n)
end

# is a the smallest element in list ss
function smallest(x,ys)
#   println("\nIn Smallest here")
  issmallest =
#     @show x
#     @show x < 0.001
    @If(x < 0.001, false,
        begin
#         println("Inside Smallest")
        issmallest = true
          for i in 1:length(ys)
#             println("Inside Smallest LOOp")
            issmallest = @If (ys[i] > 0.01) ((ys[i] >= x) & issmallest) issmallest
          end
#           println("issmallest", issmallest, " ", x, ys)
        issmallest
        end)
  issmallest
end

function bounce(p,s,o)
  v = p[:,2]
  reflection = reflect(v,o[:,2])
  new_pos = p[:,1] + p[:,2] * s
  liftedarray([new_pos reflection])
end

# Simulate a ball bouncing around an environment
function simulate(nbounces::Int64, start_pos::Point, start_dir::Vec, obs::Vector,
                  UninitArray = Array)
  # We want obstacles in parametric form
  obs = map(points_to_parametric, obstacles)

  dir  = normalise(start_dir)
  pos_dirs = Array(Any, nbounces + 1)
  pos_dirs[1] = [start_pos dir]

  # Num points in trajectory is one less the number of bounces
  npoints = nbounces + 1

  for i = 1:nbounces
    p = pos_dirs[i]
    # Find the intersection of current pos_vec and each obstacles
    ss = UninitArray(Float64, length(obs))
    for j = 1:length(obs)
      ss[j] = intersect_segments(p, obs[j])
    end
    pos_dirs[i+1] = @If(smallest(ss[1],ss), bounce(p,ss[1],obs[2]),
                              @If(smallest(ss[2],ss),bounce(p,ss[2],obs[2]),
                                  bounce(p,ss[3],obs[3])))
  end
  pos_dirs
end


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
  x = map(l->(context(units=UnitBox(0, 0, 10, 10)),
              l,
              linewidth(.5mm),
              stroke(rand_color()),
              fill(nothing)),
          all_lines)
  apply(compose,vcat(context(), x))
end

## Deterministic Examples
## ======================
obstacles = Array[[8.01 3.01; 1.02 9],
                  [0.5 3.08; 2.02 9.04],
                  [0.0 9.99; 3 5.04]]

nbounces = 4
start_pos = [3., 5.]
start_dir = [rand()*2 - 1,rand()*2 - 1]

simulation = simulate(nbounces, start_pos, start_dir, obstacles)
a = make_compose_lines(obstacles)
b = make_compose_lines(make_point_pairs(simulation))
rand_color() = RGB(rand(),rand(),rand())
draw_lines(a,b)

## Probabilistic Examples
## ======================

# s = simulate_prob(4,obstacles)
# s(Omega(Sigma.EnvVar))
# p = prob_deep(s, max_depth = 5)
# p = pre_deepening(s,T,Omega(),max_depth = 10)
# p
