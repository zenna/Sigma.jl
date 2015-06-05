using Sigma

PI = 3.1415926535897
# arc of a circle
X = uniform(-2,2)
Y = uniform(-2,2)
Z = uniform(-2,2)
cond1 = isapprox(X*X + Y*Y,0.1)
# cond2 = in(asin(X/Y), (-1/2PI,1/2PI))
cond2 = asin(X/Y) > 1/2PI
xy = PureRandArray(Any[X,Y])
samples = rand(xy,cond1&cond2,500,Sigma.pre_tlmh_parallel,Sigma.DRealSolverBinary; ncores =4 )
# samples = rand(xy,cond1&cond2,500,Sigma.pre_tlmh,Sigma.DRealSolver) 

x = [sample[1] for sample in samples]
y = [sample[2] for sample in samples]

plot(x=x,y=y,Geom.point)

# Ellipsoid
## =========
a = 2
b = 1
c = 0.5
ellip_cond = isapprox((X*X)/(a*a) + (Y*Y)/(b*b) + (Z*Z)/(c*c), 1.0,0.001)

xyz = PureRandArray(Any[X,Y,Z])
samples_ellipsoid = rand(xyz,ellip_cond,500,Sigma.pre_tlmh_parallel,Sigma.DRealSolverBinary; ncores =4 )

ellip_cond = isapprox((X*X)/(a*a) + (Y*Y)/(b*b) + (Z*Z)/(c*c), 1.0,0.001)

## Fractal
## =======
Zsqr = Z*Z
Ysqr = Y*Y
Xsqr = X*X
  
xcond = isapprox(((3Zsqr - Xsqr - Ysqr)*X*(Xsqr-3Ysqr))/(Xsqr+Ysqr),X, 0.01)
ycond = isapprox(((3Zsqr - Xsqr - Ysqr) * Y * (3*Xsqr - Ysqr))/(Xsqr+Ysqr), Y, 0.01)
zcond = isapprox(Z*(Zsqr-3*Xsqr - 3*Ysqr),Z,0.01)

samples_fractal = rand(xyz,xcond & ycond &zcond,10,Sigma.pre_tlmh_parallel,Sigma.DRealSolverBinary; ncores =4 )


cond = 
\langle x, y, z\rangle^3 = \left\langle\ \frac{(3z^2-x^2-y^2)x(x^2-3y^2)}{x^2+y^2} ,\frac{(3z^2-x^2-y^2)y(3x^2-y^2)}{x^2+y^2},z(z^2-3x^2-3y^2)\right\rangle.