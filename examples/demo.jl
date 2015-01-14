using Sigma
using Gadfly
import Sigma.Omega
x = uniform(1,0,10)
y = x + normal(2,0,1)


prob_deep(x > 0.5)
prob_deep(x > 0.5, max_depth = 10)
cond_prob_deep(x > 0.2, x < 0.1)

y = normal(1,0,2)
z = y * x
prob_deep((sqr(z) > 0.5) & (sqr(z) < 0.6))
y = uniform(0,0,1)
y
if_rv = @If z > 2 normal(2,0,3) z
cond_prob_deep(if_rv < 2, y > 0)

plot_psuedo_density(if_rv,0.,3.)

