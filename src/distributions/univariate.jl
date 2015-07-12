# uniform

uniform{T<:Real}(i::Int,a::Lift{T}, b::Lift{T}) = (b-a)*omega_component(i) + a

"univariate uniformly distributed random variable"
uniform(a::Real, b::Real) = uniform(genint(), a,b)

# Bernoulli
"univariate Bernoulli distributed random variable"
flip(i::Id, p = 0.5) = p >= omega_component(i)
flip(p) = flip(genint(), p)
flip() = flip(genint())

# Exponential
"univariate exponentially distributed random variable"
exponential(i::Id, λ) = (-log(1-omega_component(i)))/λ
exponential(λ) = exponential(genint(),λ)

# Logistic
"univariate exponentially distributed random variable"
logistic(i::Id, μ, s) = μ + s*log(omega_component(i)/(1-omega_component(i)))
logistic(μ,s) = logistic(genint(),μ,s)

# Normal
"Constructs Normally distributed random variable constructor"
function normal(i::Id, μ::Real, σ::Real)
  NormalRandVar{Float64, Float64}(i, ConstantRandVar(μ), ConstantRandVar(σ))
end