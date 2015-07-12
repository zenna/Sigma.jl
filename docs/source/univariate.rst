Primitive Univariate Random Variable
====================================

The following is a list of the primitive univariate random variables currently supported in Sigma.

.. _uniform:

Uniform Distribution
--------------------

The probability density function of a Continuous Uniform distribution over an interval :math:`[a, b]` is

.. math::

  f(x; a, b) = \frac{1}{b - a}, \quad a \le x \le b

.. function:: uniform(a::Real, b::Real)

    Returns uniformly distributed random variable between a and b

.. code-block:: julia

  uniform(a, b)    # Uniform distribution over [a, b]


.. _logistic

Logistic Distribution
---------------------

The probability density function of a Logistic distribution with location \mu and scale \beta is

.. math::

  f(x; \mu, \beta) = \frac{1}{4 \beta} \mathrm{sech}^2
  \left( \frac{x - \mu}{\beta} \right)

.. function:: logistic(μ::Real, β::Real)

    Returns logistically distributed random variable with location μ and scale β
