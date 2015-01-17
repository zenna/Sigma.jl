using Sigma
using Base.Test

# x = Sigma.uniformsmt(0,0.,1.)
# y = Sigma.uniformsmt(1,0.,1.)
# bounds = prob(x>y, box_budget = 100)
# @test bounds.l > 0.45 && bounds.u < 0.55


## Bayesian Linear Regresion
## =========================

ndatapoints = 5
xs = rand(ndatapoints)*10
ys = [2*x + 0.5 + rand(Distributions.Uniform(0,1)) for x in xs]
# plot(x = xs, y = ys)

weights = [Sigma.uniformsmt(Sigma.genint(),-10.,10.), Sigma.uniformsmt(Sigma.genint(),-10.,10.)]
yy(x,w) = sum(x .* w)
t(x,w) = yy(x,w) + Sigma.uniformsmt(Sigma.genint(),0,1)

observations = true
for i = 1:length(xs)
  observations &= t([xs[i],1.0],weights) ≊ ys[i]
end

cond_sample_mh(weights[1],observations,10)

rand(weights[1],observations)
