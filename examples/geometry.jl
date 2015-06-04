using Sigma

# arc of a circle
X = uniform(-2,2)
Y = uniform(-2,2)
cond = isapprox(X*X + Y*Y,0.1)
xy = PureRandArray(Any[X,Y])
samples = rand(xy,cond,500,Sigma.pre_tlmh_parallel,Sigma.DRealSolverBinary; ncores = 3)
x = [sample[1] for sample in samples]
y = [sample[2] for sample in samples]