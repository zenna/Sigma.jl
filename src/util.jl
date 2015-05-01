## General util TODO: Move to separate

# Are a and b equal on these fields
isequalon(a,b,fields::Vector{Symbol}) =
  all([getfield(a,f) == getfield(b,f) for f in fields])

issametype(a,b) = typeof(a) == typeof(b)

equiv{T}(a::T,b::T) =
  all([getfield(a,f) == getfield(b,f) for f in T.names])

eq_f{T}(x::T,y::T) = T.names == () ? (==) : deepequiv

function deepequiv{T}(a::T,b::T)
  for f in T.names
    if Base.isdefined(a,f) && Base.isdefined(b,f)
      same = eq_f(getfield(a,f), getfield(b,f))(getfield(a,f),getfield(b,f))
      !same && return false
    elseif Base.isdefined(a,f) $ Base.isdefined(b,f)
      return false
    end
  end
  return true
end

function deephash{T}(x::T, h = zero(Uint))
  h += uint(0x7f53e68ceb575e76)
  for t in T.names
    if Base.isdefined(x,t)
      h = hash(getfield(x,t),h)
    end
  end
  return h
end

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
