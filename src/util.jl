## General util TODO: Move to separate
type Counter
  X::Int64
end

GLOBAL_COUNTER = Counter(0)
inc(c::Counter) = c.X +=1
genint() = (inc(GLOBAL_COUNTER);GLOBAL_COUNTER.X-1)
restart_counter!() = GLOBAL_COUNTER.X = 0

tolerant_eq(a, b, epsilon = 1E-5) = abs(a - b) <= epsilon
isapprox(a, b; epsilon::Real = 1E-5) = tolerant_eq(x,y,epsilon=epsilon) #catch all
≊ = isapprox

## Arithmetic
## ==========
sqr{T <: Real}(x::T) = x * x

## =====================
## Probabilstic Utilities
rand_select(v::Vector) = v[rand(DiscreteUniform(1, length(v)))]
pnormalize{T <: Real}(v::Vector{T}) = (v/sum(v))::Vector{Float64}
