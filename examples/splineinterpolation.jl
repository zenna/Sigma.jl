# using Sigma
# using Interpolations

nx = 10
xcoarse = 1:nx
f(x) = sin(2pi/(nx-1) * (x-1)) + Sigma.uniform(0,1)
# ycoarse = f(xcoarse)

ycoarse = Any[f(x) for x in xcoarse]
ycoarsep = Sigma.RandArray(ycoarse)

yitp_linear = interpolate(ycoarsep, BSpline(Linear), OnGrid)

yitp_const = interpolate(ycoarsep, BSpline(Constant), OnCell)
yconst = RandArray([yitp_const[x] for x in xfine])

xfine = 1:.1:xcoarse[end]
ylinear = RandArray([yitp[x] for x in xfine])

using Gadfly

omega = Sigma.LazyRandomVector(Float64)

plot(
    layer(x=xcoarse,y=call(ycoarsep,omega),Geom.point),
    layer(x=xfine,y=call(yconst,omega), Geom.line,Theme(default_color=color("magenta"))),
    layer(x=xfine,y=call(ylinear,omega), Geom.line,Theme(default_color=color("red")))
)
