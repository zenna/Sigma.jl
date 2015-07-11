# Building Probabilistic Models

Building probabilistic models in Sigma is simple.  The models are made from random variable constructors.  For instance, to make a uniformly distributed random variable `x` we would write:

```julia
x = uniform(0,1)
```