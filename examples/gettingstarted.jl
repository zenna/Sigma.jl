using Sigma

# Create a uniformly distributed random variable
x = uniform(0,1)

# Sample 100 values distributed according to x
rand(x, 100)

# Compute the probability that x^2 is greater than 0.6
prob(x^2 > 0.6)

# Create another uniformly distributed random variable (independent from y)
y = uniform(0,1)

# Compute the probability that x^2 is greater than 0.6, under the condition that
# x + y < 1
prob(x^2 > 0.6, x + y < 1)

# Sample from x conditioned on x + y < 1 
rand(x, x + y < 1)
