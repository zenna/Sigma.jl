using Sigma

PI = 3.1415926535897
# arc of a circle
X = uniform(-2,2)
Y = uniform(-2,2)
Z = uniform(-2,2)
cond1 = X*X + Y*Y == 0.1
# cond2 = in(asin(X/Y), (-1/2PI,1/2PI))
cond2 = asin(X/Y) > 1/2PI
xy = RandArray(Any[X,Y])
samples = rand(xy, cond1 & cond2, 100)

# x = [sample[1] for sample in samples]
# y = [sample[2] for sample in samples]
#
# plot(x=x,y=y,Geom.point)

# Ellipsoid
## =========
a = 2
b = 1
c = 0.5
ellip_cond = ((X*X)/(a*a) + (Y*Y)/(b*b) + (Z*Z)/(c*c)) ==  1.0
xyz = RandArray(Any[X,Y,Z])
samples_ellipsoid = rand(xyz, ellip_cond, 100)

## Fractal
## =======
Zsqr = Z*Z
Ysqr = Y*Y
Xsqr = X*X

xcond = (((3Zsqr - Xsqr - Ysqr)*X*(Xsqr-3Ysqr))/(Xsqr+Ysqr)) == X
ycond = (((3Zsqr - Xsqr - Ysqr) * Y * (3*Xsqr - Ysqr))/(Xsqr+Ysqr)) == Y
zcond = (Z*(Zsqr-3*Xsqr - 3*Ysqr)) == Z
samples_fractal = rand(xyz, xcond & ycond & zcond, 10)
