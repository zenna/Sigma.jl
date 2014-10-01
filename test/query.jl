using Sigma
using Base.Test
x = Sigma.uniform(0,0,1)
y = Sigma.uniform(1,0,1)
@test Sigma.prob_deep(x+y > -0.3, max_depth = 10) == (1.0,1.0)

# Conditional probability query
@test cond_prob_deep(x+y > 1.5, y < 0.5, max_depth = 6) = (0.0,0.0)
