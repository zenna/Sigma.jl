Getting Started
===============

Starting With a Uniform Distribution
-------------------------------------
To draw 100 samples from a random variable uniformly distributed between 0 and 1.

First we need to include Sigma

.. code-block:: julia

    julia> using Sigma

Then, we create a uniform distribution ``X`` and draw samples using ``rand``:

.. code-block:: julia

    julia> X = uniform(0,1)
    RandVar{Float64}

    julia> x = rand(d, 100)
    100-element Array{Float64,1}:
      0.376264
     -0.405272
     ...