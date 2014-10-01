tolerant_eq(a,b,epsilon = 1E-5) = abs(a - b) <= epsilon

function cart_product{E}(n, A::Array{Array{E,1},1})
  lengths = [length(a) for a in A]
  elems = Array(E, length(A))
  accum_lengths = Array(Integer, length(A))
  accum_lengths[1] = prod(lengths[2:end])
  for i = 2:length(A)
    accum_lengths[i] = accum_lengths[i-1] / lengths[i]
  end

  cycle_lengths = [prod(lengths)/accum_lengths[i] for i = 1:length(A)]
  scales = cycle_lengths ./ lengths

  is = [div((n % cycle_lengths[i]),scales[i]) + 1 for i = 1:length(A)]

  for i = 1:length(A)
    elems[i] = A[i][is[i]]
  end
  elems
end

# v = Array[["a", "b"],["c", "d", "e"],["f", "g", "h", "i"]]
# v = Vector[[1, 2],[3, 4, 5],[6, 7, 8, 9]]
# cart_product(1,v)

# [cart_product(i,v) for i = 0:23]


## =====================
## Probabilstic Utilities

rand_interval{T<:Real}(a::T, b::T) = a + (b - a) * rand()
rand_select(v::Vector) = v[ceil(rand_interval(0,length(v)))]

sqr(x::Float64) = x * x
