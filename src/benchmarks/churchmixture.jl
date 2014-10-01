using Sigma
using Gadfly

a = run_church("hard.church",0.5)
a[1]["run_time"]
widths = logspace(.05,-3.008,10)
widths
numrejected = Int64[]
compiletimes = Float64[]
sampletimes = Float64[]
for width in widths
  println("doing iteratio n", width)
  a = run_church("hard.church",width)
  push!(sampletimes, a[1]["run_time"])
end
sampletimes
plot(x = widths, y = sampletimes,Geom.line, Scale.x_log10, Scale.y_log10, Scale.y_continuous(minvalue=0))
