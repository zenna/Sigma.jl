## Primitive Distributions
## =======================

typealias RV{T} Union(T, RandVar{T})

# random(i) = ω->ω[i]
random(i::Int64) = RandVarSymbolic(Float64, :(ω[$i]))

## # Distributions.jl Distribution -> RandVar by inverse transform sampling
## ================================================================================

## Location Scale Distribution Families
## ====================================
# Normal
normal(i::Int64,μ::Float64,σ::Float64) =
  RandVarSymbolic(Float64,:(quantile(Normal($μ,$σ),ω[$i])))
normal(i::Int64,μ::RV{Float64},σ::RV{Float64})= (normal(i,0.,1.) * μ) + σ
normal(μ,σ) = normal(genint(),μ, σ)

# uniform
uniform(i::Int64,a::Float64,b::Float64) =
  RandVarSymbolic(Float64,:(quantile(Uniform($a,$b),ω[$i])))
uniform(i::Int64,a::RV{Float64},b::RV{Float64}) = (b - a) * uniform(i,0.,1.) + a
uniform(a,b) = uniform(genint(),a,b)

# Bernoulli
flip{T<:Union(RandVarSymbolic{Float64},Float64)}(i::Int64,p::T) = p > random(i)
flip(i::Int64) = 0.5 > random(i)
flip{T<:Union(RandVarSymbolic{Float64},Float64)}(p::T) = p > random(genint())
flip() = 0.5 > random(genint())

# Discrete Uniform
discreteuniform(i::Int64,a::Int64,b::Int64) =
  RandVarSymbolic(Int64,:(quantile(DiscreteUniform($a,$b),ω[$i])))
discreteuniform(i::Int64,a::RV{Int64},b::RV{Int64}) =
  (b - a) * discreteuniform(i,0,1) + a
uniform(a,b) = uniform(genint(),a,b)

## Not Location Scale
## =================

gamma(i::Int64,k::Float64,theta::Float64) =
  RandVarSymbolic(Float64,:(quantile(Gamma($k,$theta),ω[$i])))
gamma(k,theta) = gamma(genint(),k,theta)

betarv(i::Int64,a::Float64,b::Float64) =
  RandVarSymbolic(Float64,:(quantile(Beta($a,$b),ω[$i])))
betarv(a,b) = betarv(genint(),a,b)

categorical(i::Int64,weights::Vector{Float64}) =
  RandVarSymbolic(Float64,:(quantile(Categorical($weights),ω[$i])))
categorical(weights) = categorical(genint(),weights)

geometric(i::Int64,weight::Float64) =
  RandVarSymbolic(Int64,:(quantile(Geometric($weight),ω[$i])))
geometric(weight) =  geometric(genint(), weight)

poission(i::Int64,lambda::Float64) =
  RandVarSymbolic(Int64,:(quantile(Poisson($lambda),ω[$i])))
poission(lambda) = poission(genint(), lambda)
