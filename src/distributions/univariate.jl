# FIXME: Move this somewhere more appropriate
convert{T <: Real, R <: Real}(::Type{SymbolicRandVar{T}}, x::R) =
  ConstantRandVar{T}(convert(T, x))

# Exponential
"exponentially distributed random variable"
exponential{T<:Real}(λ::Lift{T}, i::Id = genint()) = (-log(1-omega_component(i)))/λ

# Logistic
"Logistic exponentially distributed random variable"
logistic{T<:Real}(μ::Lift{T}, s::Lift{T}, i::Id = genint()) =
  μ + s*log(omega_component(i)/(1-omega_component(i)))

## Uniform
## =======
"univariate uniformly distributed random variable"
function uniform{T1<:Real, T2<:Real}(a::Lift{T1}, b::Lift{T2}, id::Id = genint()) 
  UniformRandVar{Float64, Float64, Float64}(id,
    convert(SymbolicRandVar{Float64},a),
    convert(SymbolicRandVar{Float64},b))
end

"Standard uniform a = 0.0, b = 1.0"
uniform(i::Id = genint()) = uniform(0.0, 1.0, i) 

## Normal
## ======
"Constructs Normally distributed random variable constructor"
function normal{T1<:Real, T2<:Real}(μ::Lift{T1}, σ::Lift{T2}, id::Id = genint()) 
  NormalRandVar{Float64, Float64, Float64}(id,
    convert(SymbolicRandVar{Float64},μ),
    convert(SymbolicRandVar{Float64},σ))
end

"Standard normal μ = 0.0 σ = 1.0"
normal(i::Id = genint()) = normal(0.0, 1.0, i) 

## Discrete Distributions
## ======================

"Bernoulli distributed random variable"
function flip{T<:Real}(p::Lift{T}, id::Int = genint()) 
  BernoulliRandVar{Bool, Float64}(id, convert(SymbolicRandVar{Float64}, p))
end

"Standard Bernoulli p = 0.5"
flip(id::Id = genint()) = normal(0.0, 1.0, id)

"Poisson distributed random variable constructor"
function poisson{T<:Real}(λ::SymbolicRandVar{T}, id::Id = genint())
  PoissonRandVar{Int64, Float64}(id, convert(SymbolicRandVar{Float64}, λ))
end 

"Standard Poisson λ = 1.0"
poisson(id::Id = genint()) = poisson(1.0, id) 