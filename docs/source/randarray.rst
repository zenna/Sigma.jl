Random Arrays
=============

Sigma.jl provides support for multivariate random variables, i.e., random arrays.
Random arrays are values of the type ``RandArray{T}``.

Fixed Size Random Array
-----------------------

The simplest (and currently only) type of random array is essentially just a normal (dense) arrays of values of type ``RandVar``.
A ``RandArray`` is created using a primitive multivariate random variable constructor.  One simple example is ``mvuniform`` where ``mv`` stands for multivariate:

.. code-block:: julia

  x = Sigma.mvuniform(0,1,10)
    RandArray{Float64}

Here ``x`` is a random array of 10 **independent** random variables uniformly distributed between 0 and 1.

Most of the normal array functions can be used with a ``RandArray``.  For instance we can inspect its size or index it with integer indices.

.. code-block:: julia

  julia> size(x)
  (10,)

  julia> x[1]
  RandVar{Float64}

But a ``RandArray`` is also a random variable and hence we can do things like sample from it:

.. code-block:: julia

  julia> rand(x)
  10-element Array{Float64,1}:
   0.558689
   0.791846
   0.874605
   0.212741
   0.476137
   0.246175
   0.7308  
   0.625276
   0.154833
   0.619555

**Note**:

- A ``RandArray`` cannot be indexed by a ``RandVar{Int}``.

Like normal arrays, A ``RandArray`` can be created with uninitialized values:

.. code-block:: julia

  Sigma.RandArray(Float64, 5,5)

A ``RandArray`` can also be initialised from a normal arrays of either constants or values of type ``RandVar``, so long as they are all of the same type.

.. code-block:: julia

  X = RandArray([uniform(0,1), exponential(0.5))])
  Y = RandArray([1.0, 3.0])