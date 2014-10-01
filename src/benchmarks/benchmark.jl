using Gadfly
using Color

# d = [0 => 0.4, 1 => 0.6]
# e = [0 => 0.6, 1 => 0.4]
# KL Divergence is a measure of the information lost when Q is used to approximate P
KL{T}(P::Dict{T, Float64}, Q::Dict{T, Float64}) = sum([log(P[i]/Q[i]) * P[i] for i in keys(P)])

function parse_output(out)
  lines = split(out,"\n")
  compile_time = lines[1][18:end]
  compile_time = int(filter(x->!(x == 'm' || x == 's'),compile_time))
  run_time = lines[2][18:end]
  run_time = int(filter(x->!(x == 'm' || x == 's'),run_time))
  data = lines[3]
  jl_data = split(data[2:end-1]," ")
  p_true = length(filter(s->s=="#t",jl_data))/length(jl_data)
  ["compile_time" => compile_time, "run_time" => run_time, "prob" => p_true]
end

function run_church(program, mhsteps = 10:30:3000)
  [parse_output(readall(`church --timed --program-args $n /home/zenna/sandbox/$program`))
   for n = mhsteps]
end

function run_church(program, n::Integer)
  parse_output(readall(`church --timed --program-args $n /home/zenna/sandbox/$program`))
end

function stat_line_layer(stats,x,y)
  x = map(stat->stat[x],stats)
  y = map(stat->stat[y],stats)
  layer(x=x,y=y,Geom.line)
end

function stat_ribbon_layer(stats,x,ylow,yhigh)
  x = map(stat->stat[x],stats)
  ymin = map(stat->stat[ylow],stats)
  ymax = map(stat->stat[yhigh],stats)
  layer(x=x,ymin=ymin,ymax=ymax,Geom.ribbon)
end

function stat_errorbar_layer(stats,x,ylow,yhigh)
  x = map(stat->stat[x],stats)
  ymin = map(stat->stat[ylow],stats)
  ymax = map(stat->stat[yhigh],stats)
  layer(x=x,ymin=ymin,ymax=ymax,y=ymin+(ymax-ymin)/2,Geom.ribbon, Geom.errorbar,
        Theme(default_color=rand_select(faint_colors)))
end

function plot_cond_performance(X::RandomVariable, Y::RandomVariable;
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

function plot_prob_performance(X::RandomVariable;
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
