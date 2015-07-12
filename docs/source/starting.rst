Getting Started
===============

First we need to include Sigma

.. code-block:: julia

    julia> using Sigma

Then, we create a uniform distribution ``x`` and draw 100 samples from it using ``rand``:

.. code-block:: julia

    julia> x = uniform(0,1)
    RandVar{Float64}

    julia> rand(x, 100)
    100-element Array{Float64,1}:
      0.376264
     -0.405272
     ...

Then we can find the probability that ``x^2`` is greater than 0.6:

.. code-block:: julia

  julia> prob(x^2 > 0.6)
  [0.225463867187499 0.225463867187499]

Then we can introduce an exponentially distributed variable ``y``, and find the probability that ``x^2`` is greater than 0.6 under the condition that the sum of ``x`` and ``y`` is less than 1

.. code-block:: julia

  julia> prob(x^2 > 0.6, x + y < 1)
  [0.054948257132298 0.05985202998882717]

Then, instead of computing conditional probabilities, we can sample from ``x`` under the same condition:

.. code-block:: julia

  julia> rand(x, x + y < 1)
  0.04740462764340371
