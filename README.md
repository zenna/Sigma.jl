# Sigma

Sigma is a probabilistic programming environment implemented in Julia.
In it, you can specify probabilistic models as normal programs, and perform inference.

# Installation

Sigma is not yet in the official Julia Package repository.  You can still easily install it from a Julia repl with

```julia
Pkg.clone("git@github.com:zenna/Sigma.jl.git")
```

# Basic Usage

## Random Variables
One of the fundamental items in Sigma is a __RandomVariable__.
RandomVariables are created using primitive RandomVariable constructors.
To create a uniformly distributed random variable use, try:

```julia
X = uniform(0,1)
```

RandomVariable constructors return RandomVariable objects, and not samples from distributions - i.e., it's not the same as `rand()`in C, nor python's `random.uniform(0,1)'.

Applying functions to RandomVariables return new RandomVariables.  In the following, `X`, `Y` and `Z` are all RandomVariables.

```julia
Y = X * X
Z = Y > 0
```

Probabilstic models are then smiply created by defining primitive RandomVariables and composing these together to create more complex ones.

## Random Arrays

RandomArrays, or multivariate random variables can be created using `RandomArray`, which takes a type as the first parameter, and a normal Julia array as the second.

```julia
RandomArray(Float64, [uniform(0,1), normal(0,2)])
```

The array can store RandomVariables which are differently distributed (e.g., uniform and normal in the above example), but they must all be only store `T`-valued.
For instance the following is *invalid*:

```julia
RandomArray(Float64, [uniform(0,1), flip(0.5)])
```

Because flip is `bool`-valued.

RandomArrays can be accessed using familiar julia style access, e.g.

```julia
X = RandomArray(Float64, [uniform(0,1), flip(0.5)])
prob(X[1] > 0.5)
```

Typical functions such as `length`,`sum`,etc produce RandomVaribles.
e.g.

```julia
X = RandomArray(Float64, [normal(0,1), normal(0.5)])
Y = sum(X)
prob(Y>1)
cond_prob(Y>1,X[1]<=0)
```

### Queries

Consructing probabilstic models is all well and good, but you can do it in any language.
What sets Sigma apart is it's ability to answer queries.
For example, given the model:

```julia
X = normal(0,1)
Y = normal(X,1)
```

We can ask what is the probability that Y is greater than 0.

```julia
prob(Y>0)
```

It will return lower and upper __probability bounds__, which the true answer must be within.

### Conditioning

Conditioning is the bread and butter of probabilstic inference.
We achieve it simply with `cond_prob`.
For example, keeping the probabilstic model above:

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

More interestingly, we can __conditionally sample__.
First we have to construct a ConditionalRandomVariable using `cond`.
We can sample from the conditional distribution simply using rand.

```julia
X = beta(0.5,0.2)
Y = normal(X,1)
Z = cond(Y, X>0.5)
rand(Z)
```

# Theory



[![Build Status](https://travis-ci.org/zenna/Sigma.jl.svg?branch=master)](https://travis-ci.org/zenna/Sigma.jl)


