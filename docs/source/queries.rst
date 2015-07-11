Inference Queries
=================

Sigma supports four kinds of inference query:

- Probability queries - probability of `X`?
- Conditional probability queries - probability of `X` given that `Y` is true
- Sampling - sample from `X`
- Conditional Sampling: sample from `X` given that `Y` is true

## Probability Queries

Probability queries are done by `prob`.  For example:


.. function:: prob(X::RandVar{Bool}, Y::RandVar{BOOl})

    Return a tuple of parameters. 

    **Note:** Let ``d`` be a distribution of type ``D``, then ``D(params(d)...)`` will construct exactly the same distribution as ``d``.

```julia
X = uniform(0,1)
Y = uniform(0,1)
prob(X + Y > 1)
```

Conditional Probability queries are also done with `prob`, but expect two boolean RandVars as input

```julia
prob(Y > 0.0,X > 0.0)
```

### Probability bounds
You may notice that Sigma returns __probability bounds__, i.e. an interval with a lower and upper bound, instead of a single number.

Sigma guarantees that the true answer is within these bounds.

Bounds are representing as intervals from the [AbstractDomains](https://github.com/zenna/AbstractDomains.jl) package.  If you really want a single point, you can use `mid` to get the midpoint between the ends.

```julia
x = prob(Y > 0.0, X > 0.0)
mid(x)
```

__Note:__

- Probability and conditional probability queries will only work for relatively low dimensional problems.  You can find the dimensionality of your problem using `ndims`.

## Sampling

To sample from any random variable use `rand`

```julia
X = exponential(0.5)
rand(X)
```

Just like `prob`, conditional sampling uses `rand` with the second argument as a `RandVar{Bool}`:

```julia
X = exponential(0.5)
rand(X, X>0.5)
```