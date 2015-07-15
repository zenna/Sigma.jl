

"univariate uniformly distributed random variable"
uniform{T<:Real}(a::Lift{T}, b::Lift{T}, i::Int = genint()) = (b-a)*omega_component(i) + a

"standard uniform between 0 amd 1"
uniform(id::Id = genint()) = uniform(0.0, 1.0, id)

# Bernoulli
"Bernoulli distributed random variable"
flip{T<:Real}(p::Lift{T} = 0.5, i::Id = genint()) = p >= omega_component(i)

# Exponential
"exponentially distributed random variable"
exponential{T<:Real}(λ::Lift{T}, i::Id = genint()) = (-log(1-omega_component(i)))/λ

# Logistic
"Logistic exponentially distributed random variable"
logistic{T<:Real}(μ::Lift{T}, s::Lift{T}, i::Id = genint()) =
  μ + s*log(omega_component(i)/(1-omega_component(i)))

"univariate uniformly distributed random variable"
function uniformx{T<:Real}(a::Lift{T}, b::Lift{T}, i::Int = genint()) 
  UniformRandVar{Float64, Float64}(i, a, b)
end

uniformx(a::Float64, b::Float64, i::Id = genint()) = 
  uniformx(ConstantRandVar(a), ConstantRandVar(b), i)

"Standard uniform a = 0.0, b = 1.0"
uniformx(i::Id = genint()) = uniformx(0.0, 1.0, i) 

@compat uniformx(a::Integer, b::Integer, i::Id = genint()) =
  uniformx(Float64(a), Float64(b), i)

# Normal
"Constructs Normally distributed random variable constructor"
function normal{T<:Real}(μ::SymbolicRandVar{T}, σ::SymbolicRandVar{T}, i::Id = genint())
  NormalRandVar{Float64, Float64}(i, μ, σ)
end 

normal(μ::Float64, σ::Float64, i::Id = genint()) = normal(ConstantRandVar(μ), ConstantRandVar(σ), i)

@compat normal(μ::Integer, σ::Integer, i::Id = genint()) = normal(Float64(μ), Float64(σ), i)

"Standard normal μ = 0.0 σ = 1.0"
normal(i::Id = genint()) = normal(0.0, 1.0, i) 

## Discrete Distributions
## ======================

# Poisson
"Constructs Poisson distributed random variable constructor"
function poisson{T<:Real}(λ::SymbolicRandVar{T}, id::Id = genint())
  PoissonRandVar{Int64, Float64}(id, λ)
end 

poisson(λ::Float64, id::Id = genint()) = poisson(ConstantRandVar(λ), id)
@compat poisson(λ::Integer, id::Id = genint()) = poisson(Float64(λ), id)

"Standard Poisson λ = 1.0"
poisson(id::Id = genint()) = poisson(1.0, id) 