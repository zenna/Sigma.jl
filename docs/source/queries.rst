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

.. function:: rand{T}(X::RandVar{T}, Y::RandVar{Bool}, n::Integer)

    Sample `n` values of type ``T`` from ``X`` conditioned on ``Y`` being true

.. code-block:: julia

  X = exponential(0.5)
  rand(X, X>0.5)

A `RandArray` can also used for the first argument to conditionally sample from:

.. function:: rand{T}(X::RandArray{T}, Y::RandVar{Bool}, n::Integer)

  Sample `n` Arrays of type ``Array{T}`` from ``X`` conditioned on ``Y`` being true

  .. code-block:: julia

    Xs = mvuniform(0,1,10)
    rand(Xs, sum(X) == 0.5)
    10-element Array{Float64,1}:
     0.997244
     0.507635
     0.503137
     0.503914
     0.504609
     0.507393
     0.500201
     0.503708
     0.501251
     0.00574937

Often times you want to sample from a collection of random variables conditioned on some proposition.
``rand`` also can take a tuple of ``RandVar`` s and ``RandArray`` s as its first argument.

.. function:: rand{T}(X::Tuple, Y::RandVar{Bool}, n::Integer)

  Sample `n` tuples of ``RandVar``s or ``RandArray``s conditioned on ``Y`` being true

  .. code-block:: julia

    Xs = mvuniform(0,1,10)
    Y = logistic(0.5, 0.5)
    rand((Y,Xs), sum(X) == Y)
    (9.941006795107837,
    [0.997761,
     0.999576,
     0.99596,
     0.997781,
     0.999121,
     0.99348,
     0.99694,
     0.998275,
     0.998735,
     0.995129])

Note: if the number of samples ``n`` is omitted, it is assumed to be 1 and only the sample (not a list of samples) is returned.

Precision
---------

Sigma solves a relaxed version of the problem you give it.  You can control how severe that relaxation is
using ``precision``.  Both ``rand`` and ``prob`` take ``precision`` as a keyword argument of type ``Float64``.
Increasing the precision will typically make the algorithms go slower, but the answer will be more precise.
For example:

.. code-block:: julia

  X = flip(0.5)
  Y = flip(0.5)
  @time prob(X & !Y; precision = 0.1)

  # A bit faster but very innacurate
  julia> @time prob(X & !Y; precision = 1.0)
  elapsed time: 0.005621369 seconds (33612 bytes allocated)
  [1.0 1.0]

  # Slower but more accurate
  @time prob(X & !Y; precision = 0.0001)
  elapsed time: 0.00789781 seconds (72828 bytes allocated)
  [0.24999999999999994 0.24999999999999994]
