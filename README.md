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
To create a random variable uniformly distributed between 0 and 1, use:

```julia
X = uniform(0.0,1.0)
```

RandomVariable constructors return values of the RandomVariable type, and not samples from distributions - i.e., it's not the same as `rand()` in Julia.Base, nor python's `random.uniform(0,1)`.
All RandomVariables have a domain type; we say for example that `uniform` returns a `Float64`-valued RandomVariable, `poission` returns a `Int64`-valued RandomVariable and `flip` returns a `Bool`-valued RandomVariable.
The domain type can be access with `domaintype`, e.g. `domaintype(flip())` will return `Bool`.

Applying functions to RandomVariables returns new RandomVariables.  In the following, `X`, `Y` and `Z` are all RandomVariables, with domaintypes `Float64`,`Float64`, and `Bool` respectively.

```julia
X = normal(0,1)
Y = X * X
Z = Y > 0
```

Complex probabilistic models are then simply created by defining primitive RandomVariables and composing these together.

## Random Arrays

Multivariate random variables can be created using `RandomArray`, which takes a type as the first parameter, and a normal Julia array as the second.

```julia
RandomArray(Float64, [uniform(0,1), normal(0,2)])
```

The array can store RandomVariables which are distributed differently (e.g., uniform and normal in the above example), but they must all be the same domain type.
For instance the following is *invalid*:

```julia
RandomArray(Float64, [uniform(0,1), flip(0.5)])
```

Because flip is `Bool`-valued.

RandomArrays can be accessed using familiar Julia array style access, e.g.:

```julia
X = RandomArray(Float64, [uniform(0,1), flip(0.5)])
prob(X[1] > 0.5)
```

Typical functions such as `length`,`sum` produce RandomVariables:

```julia
X = RandomArray(Float64, [normal(0,1), normal(0.5)])
Y = sum(X) # Float64-valued RandomVariable
```

### Queries

Consructing probabilistic models is all well and good, but you can do it in almost any language.
What sets Sigma apart is its ability to answer queries.
For example, given the model:

```julia
X = normal(0,1)
Y = normal(X,1)
```

We can ask what is the probability that Y is greater than 0.

```julia
prob(Y>0)
```

It will return lower and upper __probability bounds__, which the true probability must be within.

### Conditioning

Conditioning is the bread and butter of probabilstic inference.
We achieve it simply with `cond_prob`.
For example, keeping the probabilistic model above:

```
cond_prob(Y>0,X>0)
```

Returns the conditional probability bounds that Y>0 given X>0.

### Sampling

Oftentimes we want to sample from a RandomVariable.
To do this, use `rand`

```julia
X = beta(0.5,0.5)
rand(X)
```

will return a sample.

More interestingly, we can __conditionally sample__.
First we have to construct a ConditionalRandomVariable using `cond`.
We can sample from the conditional distribution simply using rand.

```julia
X = beta(0.5,0.2)
Y = normal(X,1)
Z = cond(Y, X>0.5)
rand(Z)
```

# Notes

- Currently only a few RandomVariable constructors - `uniform`, `normal` and `flip`, support RandomVariables as their parameters. For instance `beta(normal(0,1),normal(0,1))` is not yet supported.
- All RandomVariable constructors have methods which take an integer `i` as a first parameter, e.g.,  `uniform(0,0,1)`.  Put briefly, RandomVariables constructed with differing values of `i` will be statistically __independent__.  If this parameter is omitted, it will be randomly (and uniquely) generated for you, but in some cases this can cause a performance hit.
- RandomArrays are currently only of fixed size.
- Most query operations, e.g. `prob, cond_prob, cond` support a keyword parameter `maxdepth`.  e.g., `prob(X>0,maxdepth = 10)`.  This is an implementation detail, which eventually you should never have to worry about.  For the moment however, increasing maxdepth will result in a more precise answer.  It may be necessary, especially if you query a low probability event.

[![Build Status](https://travis-ci.org/zenna/Sigma.jl.svg?branch=master)](https://travis-ci.org/zenna/Sigma.jl)


