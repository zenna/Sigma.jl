using Gadfly
# using Sigma
# REVIEW - Decide whether plotting functions should return plot or layer
# REVIEW - Add 3D preimages. Important, not just because the look cool
#        - but because they will help with intuitions about independence
#        - and symmetry

function plot_preimage(X::RandVar{Bool};prob_args...)
  satsets, mixedsets = Sigma.pre_bfs(X, t, LazyOmega();prob_args...)
  plot_preimage(satsets)
end

function plot_preimage(X::RandVar{Bool}, dims::Vector; prob_args...)
  satsets, mixedsets = Sigma.pre_bfs(X, t, LazyOmega();prob_args...)
  plot_preimage(satsets, dims)
end

function plot_preimage(os::Vector{Omega{Interval}})
  intervals = Vector{Interval}[convert(Vector{Interval},o) for o in os]
  plot_2d_boxes(intervals)
end

function plot_preimage(os::Vector{Omega{Interval}}, dims::Vector)
  intervals = Vector{Interval}[convert(Vector{Interval},o, dims) for o in os]
  @show typeof(intervals)
  plot_2d_boxes(intervals)
end

# Returns mathematica function
function plot_preimage3D(X::RandVar{Bool};prob_args...)
  satsets, mixedsets = Sigma.pre_bfs(X, t, LazyOmega();prob_args...)
  plot_preimage3D(satsets,mixedsets)
end

function plot_preimage3D(satos::Vector{Omega{Interval}}, mixedos::Vector{Omega{Interval}})
  satintervals = Vector{Interval}[convert(Vector{Interval},o) for o in satos]
  mixedintervals = Vector{Interval}[convert(Vector{Interval},o) for o in mixedos]

  satcuboids = ["Cuboid[{$(box[1].l), $(box[2].l), $(box[3].l)}, {$(box[1].u), $(box[2].u), $(box[3].u)}]" for box in satintervals]
  mixedos = ["Cuboid[{$(box[1].l), $(box[2].l), $(box[3].l)}, {$(box[1].u), $(box[2].u), $(box[3].u)}]" for box in mixedintervals]
  "Graphics3D[{Green, Opacity[0.3],$(join(satcuboids, ",")),Blue, Opacity[1.0],$(join(mixedos, ","))},{Axes->True},{PlotRange -> {{0, 1}, {0, 1}, {0, 1}}}, {AxesLabel->{ω1,ω2,ω3}}, {ViewPoint -> Dynamic[vp]}]"
end

# Take as argument canvas range
function plot_2d_boxes(bs::Vector{Vector{Interval}};
                       abs_x_min = 0.0, abs_y_min = 0.0,
                       abs_x_max = 1.0, abs_y_max = 1.0)
  x_min = Float64[]
  y_min = Float64[]
  x_max = Float64[]
  y_max = Float64[]

  for b in bs
    push!(x_min, b[1].l)
    push!(x_max, b[1].u)
    push!(y_min, b[2].l)
    push!(y_max, b[2].u)
  end

  # Update absolumte min/max values for canvas
  abs_x_min = min(abs_x_min, minimum(x_min))
  abs_y_min = min(abs_y_min, minimum(y_min))
  abs_y_max = min(abs_y_max, maximum(y_max))
  abs_x_max = min(abs_x_max, maximum(x_max))


  plot(x_min=x_min, x_max=x_max, y_min=y_min, y_max=y_max,
       color=linspace(0,1,length(bs)),
       Theme(line_width=10.0mm,highlight_width=20.0mm),
       Geom.rectbin,
       Scale.x_continuous(minvalue=abs_x_min, maxvalue=abs_y_max),
       Scale.y_continuous(minvalue=abs_y_min, maxvalue=abs_y_max),
       Coord.cartesian(fixed=true))
end

# FIXME, REVIEW: This doesn't seem to be working
function plot_volume_hist{T}(os::Vector{Omega{T}})
  vols = Float64[Sigma.measures(o) for o in os]
  plot(x=vols, Geom.histogram, Scale.y_log10)
end

# FIXME, REVIEW: This doesn't seem to be working
function plot_volume_hist(t::Sigma.Tree)
  sat_nodes::Vector{Omega} = map(n->n.data,t.nodes)
  volumes = measures(sat_nodes)
  plot(x = volumes, Geom.histogram, Scale.y_log10)
end

function plot_density(X::RandVar, lower::Real, upper::Real;
                      n_bars = 20, progargs...)
  xs = Array{Float64}(n_bars - 1)
  ys = Array{Float64}(n_bars - 1)
  ymin = Array{Float64}(n_bars - 1)
  ymax = Array{Float64}(n_bars - 1)
  for i in 1:(n_bars - 1)
    j = i + 1
    l,u = linspace(lower,upper,n_bars)[i],linspace(lower,upper,n_bars)[j]
    prob_bounds = prob((X > l) & (X <= u); progargs...)
    ys[i] = Sigma.mid(prob_bounds)
    ymin[i] = prob_bounds.l
    ymax[i] = prob_bounds.u
    xs[i] = (u-l)/2 + l
  end
  plot(x=xs, y=ys, Scale.x_continuous(minvalue=lower, maxvalue=upper),
       Scale.y_continuous(minvalue=0),
       ymin = ymin, ymax = ymax, Geom.line, Geom.errorbar)
end

# REVIEW - DRY
function plot_cond_density(X::RandVar, Y::RandVar, lower::Real, upper::Real;
                           n_bars = 20, progargs...)
  xs = Array{Float64}(n_bars - 1)
  ys = Array{Float64}(n_bars - 1)
  ymin = Array{Float64}(n_bars - 1)
  ymax = Array{Float64}(n_bars - 1)
  for i in 1:(n_bars - 1)
    j = i + 1
    l,u = linspace(lower,upper,n_bars)[i],linspace(lower,upper,n_bars)[j]
    prob_bounds = cond_prob((X > l) & (X <= u),Y; progargs...)
    ys[i] = Sigma.mid(prob_bounds)
    ymin[i] = prob_bounds.l
    ymax[i] = prob_bounds.u
    xs[i] = (u-l)/2 + l
  end
  plot(x=xs, y=ys, Scale.x_continuous(minvalue=lower, maxvalue=upper),
       Scale.y_continuous(minvalue=0),
       ymin = ymin, ymax = ymax, Geom.line, Geom.errorbar)
end

# REVIEW - Test,
function plot_sample_density(X::RandVar, nsamples::Int64)
  samples = [rand(X) for i = 1:nsamples]
  Gadfly.plot(x = samples, Gadfly.Geom.density, Gadfly.Geom.Scale.y_continuous(minvalue=0))
end

function plot_sample_histogram(X::RandVar, nsamples::Int64)
  samples = [rand(X) for i = 1:nsamples]
  Gadfly.plot(x = samples, Gadfly.Geom.histogram, Gadfly.Geom.Scale.y_continuous(minvalue=0))
end

function plot_sample_cond_histogram(X::RandVar, Y::RandVar{Bool}, nsamples::Int64; probargs...)
  condX = conditional(X,Y; probargs...)
  samples = [rand(condX) for i = 1:nsamples]
  Gadfly.plot(x = samples, Gadfly.Geom.histogram, Gadfly.Geom.Scale.y_continuous(minvalue=0))
end

function plot_sample_cond_density(X::RandVar, Y::RandVar{Bool}, nsamples::Int64; probargs...)
  condX = conditional(X,Y; probargs...)
  samples = [rand(condX) for i = 1:nsamples]
  Gadfly.plot(x = samples, Gadfly.Geom.density, Gadfly.Geom.Scale.y_continuous(minvalue=0))
end


function plot_sat_distribution(t::Sigma.Tree)
  sat_nodes = filter(x->x.status==SAT,t.nodes)
  unsat_nodes = filter(x->x.status==UNSAT,t.nodes)
  mixed_nodes = filter(x->x.status==PARTIALSAT,t.nodes)
  println("Relative counts of SAT UNSAT AND MIXED SAT are: ", map(length, Array[sat_nodes, unsat_nodes, mixed_nodes]))
  plot(y = map(length, Array[sat_nodes, unsat_nodes, mixed_nodes]), x = ["SAT", "UNSAT", "MIXED"], Geom.bar)
end
