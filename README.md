# Sigma

Sigma is a probabilistic programming environment implemented in Julia.
In it, you can specify probabilistic models as normal programs, and perform inference.

# Installation

Sigma is not yet in the official Julia Package repository.  You can still easily install it from a Julia repl with

```julia
Pkg.clone("git@github.com:zenna/Sigma.jl.git")
```

## Random Variables
One of the fundamental items in Sigma is a __RandomVariable__.
RandomVariables are created using primitive RandomVariable constructors.
To create a uniformly distributed random variable use, try:

```julia
X = uniform(0,1)
```

RandomVariable constructors return RandomVariable objects, and not samples from distributions - i.e. it's not the same as C's `rand()` or python's `random.uniform(0,1)'.

Operations on RandomVariables return new RandomVariables.  In the following, X,Y and Z are all RandomVariables.

```julia
Y = X * X
Z = Y > 0
```

### Queries

Consructing probabilstic models is all well and good, but you can do it in any language.
What sets Sigma apart is it's ability to answer queries.

```
X = normal(0,1)
Y = normal(X,1)
prob(Y>0)
```

This will return the probability that Y is greater than 0.
More precisely, it will return lower and upper __probability bounds__, which the true answer must be within.

### Conditioning

Conditioning is the bread and butter of probabilstic inference.
We achieve it simply with `cond_prob`.
For example:

```
cond_prob(Y>0,X>0)
```

Returns the conditional probability bounds that Y>0 given X>0.

### Sampling

Oftentimes we watn to sample from a RandomVariable.
To do this, use `rand`

```julia
X = beta(0.5,0.5)
rand(X)
```

Will return a sample.

More interestingly, we can conditionally sample.
First we have to construct a ConditionalRandomVariable using `cond`.
We can sample from the conditional distribution simply using rand.

```julia
X = beta(0.5,0.2)
Y = normal(X,1)
Z = cond(Y, X>0.5)
rand(Z)
```

## Theory



[![Build Status](https://travis-ci.org/zenna/Sigma.jl.svg?branch=master)](https://travis-ci.org/zenna/Sigma.jl)


