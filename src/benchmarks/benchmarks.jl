## Benchmarking to analyse performance of algorithms

## Measures
## =======
# KL Divergence is a measure of the information lost when Q is used to approximate P
KL{T}(P::Dict{T, Float64}, Q::Dict{T, Float64}) =
  sum([log(P[i]/Q[i]) * P[i] for i in keys(P)])

function KLsafe{T}(P::Dict{T, Float64}, Q::Dict{T, Float64})
  Qnew::Dict{T,Float64} = [k => haskey(Q,k) ? Q[k] + 1 : 1 for k in keys(P)]
  totalcounts = sum(values(Qnew))
  Qnew = [k => v/totalcounts for (k,v) in Qnew] #renormalise
  KL(P,Qnew)
end

# Get the accumulative KL divergence over samples
function accumulative_KL(samples, n, groundtruth)
  kls = Array(Float64, length(samples))
  for i = 1:length(samples)
    sample_counts = vertex_distribution(samples[1:i],n)
    sample_distribution = [j => c/length(samples[1:i]) for (j,c) in sample_counts]
    kls[i] = KLsafe(groundtruth,sample_distribution)
  end
  @show kls
end

## Visualisation (TODO: move to Figure)
## ==============================
# rand_color() = RGB(rand(),rand(),rand())
# distinguished_colors = Gadfly.distinguishable_colors(10)
# faint_colors = map(c->AlphaColorValue(c,0.25), distinguished_colors)

# function stat_line_layer(stats,x,y)
#   x = map(stat->stat[x],stats)
#   y = map(stat->stat[y],stats)
#   layer(x=x,y=y,Geom.line)
# end

# function stat_ribbon_layer(stats,x,ylow,yhigh)
#   x = map(stat->stat[x],stats)
#   ymin = map(stat->stat[ylow],stats)
#   ymax = map(stat->stat[yhigh],stats)
#   layer(x=x,ymin=ymin,ymax=ymax,Geom.ribbon)
# end

# function stat_errorbar_layer(stats,x,ylow,yhigh)
#   x = map(stat->stat[x],stats)
#   ymin = map(stat->stat[ylow],stats)
#   ymax = map(stat->stat[yhigh],stats)
#   layer(x=x,ymin=ymin,ymax=ymax,y=ymin+(ymax-ymin)/2,Geom.ribbon, Geom.errorbar,
#         Theme(default_color=rand_select(faint_colors)))
# end

function plot_cond_performance(X::RandVar, Y::RandVar;
                               num_points = 10, max_depth = 10,
                               max_boxes = 300000)
  box_budget = linspace(1,max_boxes,num_points)
  probs = Array((Float64,Float64), length(box_budget))
  times = Array(Float64, length(box_budget))
  for i = 1:num_points
    tic()
    println("num_points", i)
    probs[i] = cond_prob_deep(X, Y, max_depth = max_depth, box_budget = box_budget[i])
    times[i] = toc() * 1000
  end
  probmins = map(x->(xn = x[1];if isnan(xn) 0.0 else xn end),probs)
  probmaxs = map(x->(xn = x[2];if isnan(xn) 1.0 else xn end),probs)
  probmins,probmaxs,times,probs
  [["probmin" => probmins[i], "probmax" => probmaxs[i], "run_time" => times[i]]
   for i = 1:num_points]
end

function plot_prob_performance(X::RandVar;
                               num_points = 10, max_depth = 10,
                               max_boxes = 300000)
  box_budget = linspace(1,max_boxes,num_points)
  probs = Array((Float64,Float64), length(box_budget))
  times = Array(Float64, length(box_budget))
  for i = 1:num_points
    tic()
    probs[i] = prob_deep(X, max_depth = max_depth, box_budget = box_budget[i])
    times[i] = toc() * 1000
  end
  probmins = map(x->(xn = x[1];if isnan(xn) 0.0 else xn end),probs)
  probmaxs = map(x->(xn = x[2];if isnan(xn) 1.0 else xn end),probs)
  probmins,probmaxs,times,probs
  [["probmin" => probmins[i], "probmax" => probmaxs[i], "run_time" => times[i]]
   for i = 1:num_points]
end

function add_KL!(stats, groundtruth::Dict)
  for s in stats
    kl1 = KL(groundtruth, ptrue_to_dist(s["probmin"]))
    kl2 = KL(groundtruth, ptrue_to_dist(s["probmax"]))
    s["klmin"] = min(kl1,kl2)
    s["klmax"] = max(kl1,kl2)
  end
  stats
end

function add_KL_church!(stats, groundtruth::Dict)
  for s in stats
    kl = KL(groundtruth, ptrue_to_dist(s["prob"]))
    s["kl"] = kl
  end
  stats
end

include("solvers.jl")
include("geometry.jl")
include("vis.jl")
include("simplex/simplex.jl")
include("motionplanning/motionplanning.jl")
include("run.jl")
