## =============
# Visualisation
using Gadfly
using Color

rand_color() = RGB(rand(),rand(),rand())
distinguished_colors = Gadfly.distinguishable_colors(10)
faint_colors = map(c->AlphaColorValue(c,0.25), distinguished_colors)

function plot_2d_boxes{B <:Box}(bs::Vector{B})
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

  plot(x_min=x_min, x_max=x_max, y_min=y_min,color=rand(length(bs)), y_max=y_max,Geom.rectbin)
end

function plot_volume_distribution(bs::Vector{Box})
  vols = map(volume,preimage)
  plot(x=vols, Geom.histogram)
end

function plot_density(rv::RandomVariable, lower::Float64, upper::Float64; n_bars = 20, max_depth = 13)
  xs = Array(Float64,n_bars - 1)
  ys = Array(Float64,n_bars - 1)
  ymin = Array(Float64,n_bars - 1)
  ymax = Array(Float64,n_bars - 1)
  for i in 1:(n_bars - 1)
    j = i + 1
    l,u = linspace(lower,upper,n_bars)[i],linspace(lower,upper,n_bars)[j]
    prob_bounds = prob_deep((rv > l) & (rv < u),max_depth=max_depth)
    ys[i] = mean(prob_bounds)
    ymin[i] = prob_bounds[1]
    ymax[i] = prob_bounds[2]
    xs[i] = (u-l)/2 + l
  end
  plot(x=xs, y=ys, Scale.x_continuous(minvalue=lower, maxvalue=upper),
       Scale.y_continuous(minvalue=0),
       ymin = ymin, ymax = ymax, Geom.line, Geom.errorbar)
end

function plot_cond_density(X::RandomVariable, Y::RandomVariable, lower::Float64, upper::Float64; n_bars = 20, max_depth = 10)
  xs = Array(Float64,n_bars - 1)
  ys = Array(Float64,n_bars - 1)
  ymin = Array(Float64,n_bars - 1)
  ymax = Array(Float64,n_bars - 1)
  for i in 1:(n_bars - 1)
    j = i + 1
    l,u = linspace(lower,upper,n_bars)[i],linspace(lower,upper,n_bars)[j]
    prob_bounds = cond_prob_deep((X > l) & (X < u),Y,max_depth=max_depth)
    ys[i] = mean(prob_bounds)
    ymin[i] = prob_bounds[1]
    ymax[i] = prob_bounds[2]
    xs[i] = (u-l)/2 + l
  end
  plot(x=xs, y=ys, Scale.x_continuous(minvalue=lower, maxvalue=upper),
       Scale.y_continuous(minvalue=0),
       ymin = ymin, ymax = ymax, Geom.line, Geom.errorbar)
end

function plot_sample_cond_density(X::RandomVariable, Y::RandomVariable,
                                  numsamples::Integer; max_depth = 10)
  sampler = cond_sample(X,Y,max_depth = max_depth)
  samples = [sampler(100) for i = 1:numsamples]
  samples = map(x->x[1],samples)
  Gadfly.plot(x = samples, Gadfly.Geom.histogram, Gadfly.Geom.Scale.y_continuous(minvalue=0))
end

function plot_sat_distribution(t::Tree)
  sat_nodes = filter(x->x.status==SAT,t.nodes)
  unsat_nodes = filter(x->x.status==UNSAT,t.nodes)
  mixed_nodes = filter(x->x.status==MIXEDSAT,t.nodes)
  println("Relative counts of SAT UNSAT AND MIXED SAT are: ", map(length, Array[sat_nodes, unsat_nodes, mixed_nodes]))
  plot(y = map(length, Array[sat_nodes, unsat_nodes, mixed_nodes]), x = ["SAT", "UNSAT", "MIXED"], Geom.bar)
end

function plot_volume_distribution(t::Tree)
  sat_nodes::Vector{Omega} = map(n->n.data,t.nodes)
  volumes = measure(sat_nodes)
  plot(x = volumes, Geom.histogram, Scale.y_log10)
end

function plot_omega_samples(X::RandomVariable)
  xs = Float64[]
  ys = Float64[]
  for x in linspace(0.0,1.0,100)
    for y in linspace(0.0,1.0,100)
      if X([x,y])
        push!(xs,x)
        push!(ys,y)
      end
    end
  end
  plot(x=xs,y=ys)
end
