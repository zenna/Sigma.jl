# Sigma

Sigma is a probabilistic programming environment implemented in Julia.
In it, you can specify probabilistic models as normal programs, and perform inference.

[![Build Status](https://travis-ci.org/zenna/Sigma.jl.svg?branch=master)](https://travis-ci.org/zenna/Sigma.jl)

# Installation

Sigma is built on top of Julia.  We recommend using [IJulia](https://github.com/JuliaLang/IJulia.jl) as an interface.

Sigma is not yet in the official Julia Package repository.  You can still easily install it from a Julia repl with

```julia
Pkg.clone("git@github.com:zenna/Sigma.jl.git")
```

Sigma is then loaded with

```julia
using Sigma
``` 

# Basic Usage

## Random Variables
One of the fundamental items in Sigma is a random variable.
These are represented with the `RandVar` Julia type.
RandVars are created using primitive RandVar constructors.
To create a random variable uniformly distributed between 0 and 1, use:

```julia
X = uniform(0.0,1.0)
```

RandVar constructors return values of the RandVar type, and not samples from distributions - i.e., it's not the same as `rand()` in Julia.Base, nor python's `random.uniform(0,1)`.
All RandVars have a range type; we say for example that `uniform` returns a `Float64`-valued RandVar, `poission` returns a `Int64`-valued RandVar and `flip` returns a `Bool`-valued RandVar.
The range type can be access with `rangetype`, e.g. `rangetype(flip())` will return `Bool`.

Applying functions to RandVars returns new RandVars.  In the following, `X`, `Y` and `Z` are all RandVars, with rangetypes `Float64`,`Float64`, and `Bool` respectively.

```julia
X = normal(0.0,1.0)
Y = X * X
Z = Y > 0.0
```

Complex probabilistic models are then simply created by defining primitive RandVars and composing these together.

## Random Arrays

Multivariate random variables can be created using `RandArray`, which takes a normal Julia array of RandVars.

```julia
RandArray([uniform(0.0,1.0), normal(0.0,2.0)])
```

The array can store RandVars which are distributed differently (e.g., uniform and normal in the above example), but they must all be the same domain type.
For instance the following is *invalid*:

```julia
RandArray([uniform(0.0,1.0), flip(0.5)])
```

Because flip is `Bool`-valued.

RandArrays can be accessed using familiar Julia array style access, e.g.:

```julia
X = RandArray([uniform(0.0,1.0), normal(0.0,2.0)])
Y = X[1] + X[2]
```

Typical functions such as`sum` produce RandVars:

```julia
X = RandArray([normal(0.0,1.0), normal(0.5,0.8)])
Y = sum(X) # Float64-valued RandVar
```

All RandVar constructors have methods which take an integer `i` as a first parameter, e.g.,  `uniform(0,0.0,1.0)`.  Put briefly, RandVars constructed with differing values of `i` will be statistically __independent__.  If this parameter is omitted, it will be randomly (and uniquely) generated for you, but in some cases this can cause a performance hit.

__Note__: RandArrays are currently only of fixed size.

## Queries

Consructing probabilistic models is all well and good, but you can do it in almost any language.
What sets Sigma apart is its ability to answer queries.
For example, given the model:

```julia
X = normal(0.0,1.0)
Y = normal(X,1.0)
```

We can ask what is the probability that Y is greater than 0.

```julia
prob(Y > 0.0)
```

It will return lower and upper __probability bounds__, which the true probability must be within.

### Conditioning

Conditioning is the bread and butter of probabilstic inference.
We achieve it simply with `cond_prob`.
For example, keeping the probabilistic model above:

```
cond_prob(Y > 0.0,X > 0.0)
```

Returns the conditional probability bounds that Y>0 given X>0.

### Sampling

Oftentimes we want to sample from a RandVar.
To do this, use `rand`

```julia
X = betarv(0.5,0.5)
rand(X)
```

will return a sample.

More interestingly, we can __conditionally sample__.
This is done with `rand(X,Y)` or `rand(X,Y,nsamples)`.

```julia
X = betarv(0.5,0.2)
Y = normal(X,1.0)
tensamples = rand(Y,X>0.5,10)
```

### Query parameters

Most query operations, e.g. `prob, cond_prob, cond` support a keyword parameter `box_budget`.  e.g., `prob(X > 0, boxbudget = 1E5)`.  This is an implementation detail, which eventually you should never have to worry about.  For the moment however, increasing box_budget will result in a more precise answer.
A second parameter is `max_iters`, which controls how many iterations of the refinement (until `box_budget` is reached) to do.  If you increase `box_budget` you may need to also increase `max_iters` to hit that budget.

Other functions which use preimage computations (such as plotting as described below) will often also take these same parameters as input

## Primitive Distributions

Currently primitive distributions are split between those which can take random variables as parameters, and those wihch cannot.
In the former category:

```julia
normal(μ::Float64,σ::Float64)
uniform(i::Int64,a::Float64,b::Float64)
flip(weight::Float64)
discreteuniform(a::Int64,b::Int64)
```

In the latter category:

```
gamma(k::Float64,theta::Float64)
betarv(a::Float64,b::Float64) =
categorical(weights::Vector{Float64}) =
geometric(weight::Float64) =
poission(lambda::Float64)
```

## Plotting
To plot we have to load the plotting functions.  This is not done by default because they take a long time to initialise.  To load use

```julia
loadvis()
```

We can plot an (unnormalised) density of a Float64-valued RandVar using `plot_density`

```julia
X = betarv(0.5,0.5)
plot_density(X,0,1)
```

This plot is created by evaluating splitting the range of the variable into many small intervals, and running a probability query for each interval.  We can plot conditional using `plot_cond_density`.

We can also plot using samples `plot_sample_density` and `plot_sample_cond_density` which takes the number of samples as the last argument.  This density is estimated using kernal density estimation.  If we instead you want a histogram, use `plot_sample_histogram` or `plot_sample_cond_histogram`.

Finally you can plot preimage of a `Bool`-valued RandVar using `plot_preimage`.

```julia
X = normal(0.0,1.0)
Y = uniform(0.0,1.0)
plot_preimage(X > Y)
```

If your model defines preimages with more than two dimensions, you can project these to 2D by supplying an array of the two dimensions you wish to project as the last argument.

```julia
A = betarv(1,0.5,0.5)
B = normal(2,0.0,1.0)
C = uniform(3,0.0,1.0)
plot_preimage(A + B > C, [1,2])
```

Note here that all the random variables are constructed using the explicit first integer parameter, as described above.
This allows us to choose a meaningful projection of the sample space, because the dimensions of the sample space are linked to the random variables which map from them.
