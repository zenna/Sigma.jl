## General util TODO: Move to separate
type Counter
  X::Int64
end

GLOBAL_COUNTER = Counter(0)
inc(c::Counter) = c.X +=1
genint() = (inc(GLOBAL_COUNTER);GLOBAL_COUNTER.X-1)
restart_counter!() = GLOBAL_COUNTER.X = 0

isapprox(a, b; epsilon = DEFAULT_PREC) = abs(a - b) <= epsilon
≊ = isapprox
≊
## Arithmetic
## ==========
sqr{T <: Real}(x::T) = x * x

## =====================
## Probabilstic Utilities
rand_select(v::Vector) = v[rand(DiscreteUniform(1, length(v)))]
pnormalize{T <: Real}(v::Vector{T}) = (v/sum(v))::Vector{Float64}

## Type stuff
fields(X) = [getfield(X, field) for field in fieldnames(X)]

## Printing
fmt = "%.32f"
@eval dofmt(x) = @sprintf($fmt, x)