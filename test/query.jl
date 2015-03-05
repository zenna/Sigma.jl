using Sigma
using Base.Test
import Sigma:domaineq
x = Sigma.uniform(0,0,1)
y = Sigma.uniform(1,0,1)
@test domaineq(prob(x+y > - 1.0), Interval(1.0,1.0))

# Conditional probability query
@test domaineq(cond_prob(x+y > 1.5, y < 0.5),Interval(0.0,0.0))
