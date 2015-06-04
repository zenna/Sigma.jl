using Sigma

PI = 3.1415926535897
# arc of a circle
X = uniform(-2,2)
Y = uniform(-2,2)
cond1 = isapprox(X*X + Y*Y,0.1)
# cond2 = in(asin(X/Y), (-1/2PI,1/2PI))
cond2 = asin(X/Y) > 1/2PI
xy = PureRandArray(Any[X,Y])
samples = rand(xy,cond1&cond2,500,Sigma.pre_tlmh,Sigma.DRealSolverBinary)
# samples = rand(xy,cond1&cond2,500,Sigma.pre_tlmh,Sigma.DRealSolver) 

x = [sample[1] for sample in samples]
y = [sample[2] for sample in samples]