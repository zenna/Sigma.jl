## Primitive Distributions
## =======================
# random(i) = ω->ω[i]
random(i::Int64) = RandomVariableSymbolic(Float64, :(ω -> ω[$i]))

## # Distributions.jl Distribution -> RandomVariable by inverse transform sampling
## ================================================================================

# Normal
normal(i::Int64,μ::Float64,σ::Float64) =
  RandomVariableSymbolic(Float64,:(ω -> quantile(Normal($μ,$σ),ω[$i])))
normal(i::Int64,μ::RandomVariableSymbolic{Float64},σ::RandomVariableSymbolic{Float64})= (normal(i,0.,1.) * μ) + σ
normal(μ,σ) = normal(genint(),μ, σ)

# uniform
uniform(i::Int64,a::Float64,b::Float64) = RandomVariableSymbolic(Float64,:(ω -> quantile(Uniform($a,$b),ω[$i])))
uniform(i::Int64,a::RandomVariableSymbolic{Float64},b::RandomVariableSymbolic{Float64}) = (b - a) * uniform(i,0,1) + a
uniform(a,b) = uniform(genint(),a,b)

# Bernoulli
flip{T<:Union(RandomVariableSymbolic{Float64},Float64)}(i::Int64,p::T) = p > random(i)
flip(i::Int64) = 0.5 > random(i)
flip() = 0.5 > random(genint())
flip{T<:Union(RandomVariableSymbolic{Float64},Float64)}(p::T) = p > random(genint())
# randomize{D <: Distribution}(i, d::D) = quantile(d, random(i))

## Convenience Random Variable Constructors
# normal(i::Int64,μ,σ) = randomize(i,Normal(μ,σ))
# normal(μ,σ) = normal(genint(),μ, σ)
# uniform(i::Int64,a,b) = randomize(i, Uniform(a,b))
# uniform(a,b) = uniform(genint(),a,b)
# chi(i::Int64,df) = randomize(i, Chi(df))
# chi(df) = chi(genint(),df)
# discreteuniform(i::Int64,a,b) = randomize(i,DiscreteUniform(a,b))
# discreteuniform(a,b) = discreteuniform(genint(),a,b)
# gamma(i::Int64,k,theta) = randomize(i,(Gamma(k,theta)))
# gamma(k,theta) = gamma(genint(),k,theta)
# categorical(i::Int64,weights::Vector) = randomize(i,(Categorical(weights)))
# categorical(weights) = categorical(genint(),weights)
# geometric(i::Int64,weight) =  randomize(i,(Geometric(weight)))
# geometric(weight) =  geometric(genint(),weight)
# poission(i::Int64,lambda) = randomize(i,Poisson(lambda))
# poission(lambda) = poission(genint(), lambda)

# flip(i::Int64) = 0.5 > random(i)
# flip() = 0.5 > random(genint())
# flip(i::Int64,p) = p > random(i)
# flip(p) = p > random(genint())
