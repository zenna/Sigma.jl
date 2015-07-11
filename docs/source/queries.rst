Inference Queries
=================

Sigma supports four kinds of inference query:

- Probability Queries - probability of ``X``
- Conditional probability Queries - probability of ``X`` given that ``Y`` is true
- Sampling - sample from ``X``
- Conditional Sampling: sample from ``X`` given that ``Y`` is true

Probability Queries
-------------------
Probability queries are done by ``prob``:

.. function:: prob(X::RandVar{Bool})

    Return a the probability that X is true.
    Returns an interval :math:`I = [a,b]`, such that :math:`a \leq P(X) \leq b`.

.. code-block:: julia

  X = uniform(0,1)
  Y = uniform(0,1)
  prob(X + Y > 1)

Conditional Probability Queries
-------------------------------
Conditional probability queries are also done with ``prob``, but it expects two boolean RandVars as input:

.. function:: prob(X::RandVar{Bool}, Y::RandVar{Bool})

    Return :math:`P(X \vert Y)` : the conditional probability that X is true given Y is true.
    Returns an interval :math:`I = [a,b]` such that :math:`a \leq P(X \vert Y) \leq b`.

.. code-block:: julia

  X = uniform(0,1)
  Y = uniform(0,1)
  prob(Y > 0.0,X > 0.0)

Probability bounds
------------------

As described above, a (conditional) probability query returns a **probability bound**, i.e. an interval with a lower and upper bound, instead of a single number.  Sigma guarantees that the true answer is within these bounds.

Bounds are representing as intervals from the `AbstractDomains <https://github.com/zenna/AbstractDomains.jl>`_ package.  If you really want a single point, you can use ``mid`` to get the midpoint between the ends.

.. code-block:: julia

  x = prob(Y > 0.0, X > 0.0)
  mid(x)

**Note:**

- Probability and conditional probability queries will only work for relatively low dimensional problems (less than around 10).  You can find the dimensionality of a random variable using ``ndims``.

.. code-block:: julia

  julia> X = uniform(0,1)
  RandVar{Float64}

  julia> Y = uniform(0,1)
  RandVar{Float64}

  julia> Z = X + Y
  RandVar{Float64}

  julia> ndims(Z)
  2


Sampling
---------

To sample from any random variable use ``rand``

.. function:: rand{T}(X::RandVar{T})

    Sample a value of type ``T`` from ``X``

.. code-block:: julia
  
  X = exponential(0.5)
  rand(X)


Conditional Sampling
--------------------

Just like ``prob``, to conditionally sample use ``rand`` with the second argument with the ``RandVar{Bool}`` you want to condition on:

.. function:: rand{T}(X::RandVar{T}, Y::RandVar{Bool})

    Sample a value of type ``T`` from ``X`` conditioned on ``Y`` being true

.. code-block:: julia

  X = exponential(0.5)
  rand(X, X>0.5)