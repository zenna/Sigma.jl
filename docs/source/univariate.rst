Primitive Univariate Random Variable
====================================

The following is a list of the primitive univariate random variables currently
supported in Sigma.  In addition to categorising random variables by their output
type, we distinguish between random variables which can and cannot be expressed
in closed form.  This is because there are currently restrictions
on where random variables without a closed form solution (e.g. normal) can be
used.

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

The probability density function of a Logistic distribution with location μ and scale β is

.. math::

  f(x; \mu, \beta) = \frac{1}{4 \beta} \mathrm{sech}^2
  \left( \frac{x - \mu}{\beta} \right)

.. function:: logistic(μ::Real, β::Real)

    Returns logistically distributed random variable with location μ and scale β

.. _normal

Normal Distribution
-------------------

The probability density function of a Normal distribution with mean μ and variance σ is

.. math::

  f(x; \mu, \sigma) = \frac{1}{\sqrt{2 \pi \sigma^2}}
  \exp \left( - \frac{(x - \mu)^2}{2 \sigma^2} \right)

.. function:: normal(μ::Real, σ::Real)

    Returns normally distributed random variable with location μ and scale β

.. code-block:: julia

  a = normal()          # standard Normal distribution with zero mean and unit variance
  b = normal(mu)        # Normal distribution with mean mu and unit variance
  normal(mu, sig)       # Normal distribution with mean mu and variance sig^2
  normal(a,b)           # Normal distribution with normal parameters
