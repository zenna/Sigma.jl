using Sigma
using Gadfly
using DataFrames
import Gadfly: plot, Geom

function plot_2d_boxes2(bs)
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

  plot(x_min=x_min, x_max=x_max, y_min=y_min, y_max=y_max,
       Geom.rectusing Distributions
Gamma(3,2)
bin)
end


const DRAW_DIR = "/home/zenna/Dropbox/writing/aaai2/AuthorKit/figures/"

# Truncated Mixture
m1mean = 0.
m2mean = 20
m1 = Sigma.normal(0,m1mean,2)
m2 = Sigma.normal(1,m2mean,1)

truncated(m,mean,dev) = (m  < (mean + dev)) & (m  > (mean - dev))
mix = Sigma.@If Sigma.flip(3,0.5) m1 m2
mix_plot = Sigma.plot_cond_density(m1,m1<2.,
                                   0.,2.5, n_bars = 50, max_depth = 30)
# mixsampler = cond_sample(mix,mix>0,max_depth = 30)
sampler = Sigma.cond_sample(mix,truncated(m1,m1mean,.10) & truncated(m2,m2mean,10),max_depth = 30)

numrejected = Int64[]
compiletimes = Float64[]
sampletimes = Float64[]
widths = logspace(.05,-4.008,20)
for width in widths
  tic()
  sampler = cond_sample(mix,truncated(m1,m1mean,width) & truncated(m2,m2mean,width),max_depth = 13)
  compiletime = toc()
  tic()
  samples = [sampler(100) for i = 1:100]
  sampletime = toc()
  rejected = 0
  push!(numrejected, rejected)
  push!(compiletimes, compiletime)
  push!(sampletimes, sampletime)
end

numrejected = Int64[]
compiletimes = Float64[]
sampletimes = Float64[]
widths = logspace(.05,-4.008,20)
x = [sampler(100) for i = 1:100]
for max_depth in 4:20
  width = .05
  tic()
  sampler = Sigma.cond_sample(mix,truncated(m1,m1mean,width) & truncated(m2,m2mean,width),max_depth = max_depth)
  compiletime = toc()
  tic()
  samples = [sampler(500) for i = 1:100]
  sampletime = toc()
  rejected = sum([xx[2] for xx in samples])
  push!(numrejected, rejected)
  push!(compiletimes, compiletime)
  push!(sampletimes, sampletime)
end
numrejected

church_widths = [1.1220184543019633,0.5131238749148365,0.23466290594250525,0.10731654112668315,0.04907822969778109,0.022444560782338425,0.010264394453797104,0.004694134785032036,0.0021467317413835763,0.0009817479430199844]
church_sampletimes = [244.0,230.0,232.0,231.0,256.0,381.0,247.0,425.0,15904.0,126498.0]

(sampletimes*1000)

plot(x=[widths], y=[(sampletimes*1000)],Geom.line)


tan = plot([sin, tan], 0, 25)
draw(SVG(string(DRAW_DIR,"tan2.svg"), 4inch, 3inch), tan)
draw(SVG(string(DRAW_DIR,"churchfail.svg"), 4inch, 3inch), churchfail)



churchfail = plot(layer(x=widths, y=(sampletimes*1000),Geom.line),
     layer(x=widths, y=(compiletimes*1000),Geom.line),
     layer(x=church_widths, y=church_sampletimes,Geom.line),
     Scale.x_log10, Scale.y_continuous(minvalue=0))
plot(x=, Geom.histogram, Scale.y_continuous(minvalue=0))


m3 = Sigma.normal(0,0,1)
m4 = Sigma.normal(1,0,1)
dist = Sigma.uniform(2,5,15)
m3t = m3 + dist
mix2 = Sigma.@If Sigma.flip(3,0.5) m3t m4
mix_plot2 = Sigma.plot_cond_density(mix2,(m4 - m3) < 10,
                                   0.,20., n_bars = 50, max_depth = 30)

# Gaussians on unit circle

nary_to_unary(f::Function) = x->apply(f,to_intervals(x))
## Restrict to epsilon thick circle
circle(radius, x, y) =  tolerant_eq(sqrt(sqr(x+0.001) + sqr(y-0.001)), radius, 0.1)
plot_2d_boxes(circle_pre)

x = Sigma.uniform(0,2,4)
y = Sigma.uniform(1,.5,6)

plot_psuedo_density(x/y,0.,10.,n_bars = 40)

# Preimage Figures
x = Sigma.normal(2,0,2)
y = Sigma.normal(1,0,1)
@time prob_deep(rv,max_depth = 10)
rv = (y>(x+2.001)) | (y<(x-2.001))
pre

function tosatboxes(pre)
  sat =  Sigma.sat_tree_data(pre)
  map(x->convert(NDimBox,collect(values(x.intervals))),sat)
end

function tomixedboxes(pre)
  mixed =  Sigma.mixedsat_tree_data(pre)
  map(x->convert(NDimBox,collect(values(x.intervals))),mixed)
end

function doplots(rv,depths)
  plots = Plot[]
  names = String[]
  for d in depths, lh in [tosatboxes, tomixedboxes]
    pre = Sigma.pre_deepening(rv, Sigma.T, Sigma.Omega(),max_depth = d)
    sat_data = lh(pre)
#       mixed =  Sigma.mixedsat_tree_data(pre)
#       sat =  Sigma.sat_tree_data(pre)
#       mixed_boxes = map(x->convert(NDimBox,collect(values(x.intervals))),mixed)
#       sat_boxes = map(x->convert(NDimBox,collect(values(x.intervals))),sat)
    push!(plots,plot_2d_boxes2(sat_data))
    push!(names, "$lh-d$d")
    plot_2d_boxes2(sat_data)
  end
  plots,names
end

function saveplots(plots,names)
  for i = 1:length(plots)
    name = names[i]
    draw(SVG(string(DRAW_DIR,"$name 2.svg"), 4inch, 3inch), plots[i])
  end
end

a,b = doplots(rv, [5, 7])
saveplots(a,b)
plots,names = doplots(rv, [5, 10])
names

