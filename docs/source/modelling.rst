Building Probabilistic Models
-----------------------------

Building probabilistic models in Sigma is simple.  A probabilistic model is simply a random variable.  Sigma provides a collection of functions which return random variables.  Arguably the simplest random variable is the standard uniform, which is created by ``uniform``:

.. code-block:: julia

  x = uniform(0,1)
   RandVar{Float64}

Random variables are values of the ``RandVar{T}`` type, which is paramterised by ``T``.  There are many ways to think about random variables, but for the most part you can treat them as if they were values of the type ``T``.  That is, you can treat a ``RandVar{Float64}`` as if it were a ``Float64``.  For example, you can apply primitive functions to them:

.. code-block:: julia

  x = uniform(0,1)
  y = uniform(0,1)
  x + y
    RandVar{Float64}


Notice ``x + y`` is also a random variable.  When you apply functions to random variables which treat them as if they were numbers (e.g. ``+``, ``-``, ``/``, ...), you will get back a random variable of the appropriate type.

Of course Sigma has random variables of type other than ``Float64``.  To sample from a Bernoulli distribution use ``flip`` (named so because it is like flipping a coin):

.. code-block:: julia

  x = flip(0.6)
    RandVar{Bool}

Similarly boolean functions can be applied to ``RandVar{Bool}``

.. code-block:: julia

  x = flip(0.3)
  y = flip(0.6)
  z = x & y

**Note**: Short-cut operators like ``&&``, ``||``, ``?`` and ``if`` cannot be used with ``RandVar{Bool}``.  This is a tricky limitation we are trying to solve.

With these tools we can now make a more complex model:

.. code-block:: julia

  a = logistic(0.5, 0.5)
  x = uniform(0,1)
  y = exponential(x)

  z = ifelse((y > 0.4) | flip(0.3), sin(a), atan(x+y)^3)