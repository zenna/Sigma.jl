# Sigma

Sigma is a probabilistic programming environment implemented in Julia.
You can use it to specify probabilistic models as normal Julia programs, and perform inference.

[![Build Status](https://travis-ci.org/zenna/Sigma.jl.svg?branch=master)](https://travis-ci.org/zenna/Sigma.jl)

# Installation

Sigma is built on top of Julia.  Sigma is currently highly unstable and hence not yet in the official Julia Package repository.  You can still (try to) install it from a Julia REPL with

```julia
Pkg.clone("https://github.com/zenna/Sigma.jl.git")
```

Sigma is then loaded with

```julia
using Sigma
```

# Usage

[Read the documentation](http://sigmajl.readthedocs.org/en/latest/) or see the quick start belong

# Quick Start
First we need to include Sigma

```julia
julia> using Sigma
```

Then, we create a uniform distribution ``x`` and draw 100 samples from it using ``rand``:

```julia
julia> x = uniform(0,1)
RandVar{Float64}

julia> rand(x, 100)
100-element Array{Float64,1}:
  0.376264
  0.492391
     ...
```

Then we can find the probability that ``x^2`` is greater than 0.6:

```julia
julia> prob(x^2 > 0.6)
[0.225463867187499 0.225463867187499]
```
Then we can introduce an exponentially distributed variable ``y``, and find the probability that ``x^2`` is greater than 0.6 under the condition that the sum of ``x`` and ``y`` is less than 1

```julia
julia> y = exponential(0.5)
julia> prob(x^2 > 0.6, x + y < 1)
[0.053548951048950494 0.06132144691466614]
```

Then, instead of computing conditional probabilities, we can sample from ``x`` under the same condition:

```julia
julia> rand(x, x + y < 1)
0.04740462764340371
```
