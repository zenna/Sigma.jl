# uniform

uniform{T<:Real}(i::Int,a::Lift{T}, b::Lift{T}) = (b-a)*omega_component(i) + a
uniform(a::Real, b::Real) = uniform(genint(), a,b)

# Bernoulli
flip(i::Int, p::Lift{Real}) = p >= omega_component(i)
flip(i::Int) = 0.5 >= omega_component(i)
flip(p::Lift{Real}) = flip(genint(), p)
flip() = flip(genint())

# Exponential
exponential(i::Int, λ::Lift{Real}) = (-log(1-omega_component(i)))/λ
exponential(λ::Lift{Real}) = exponential(genint(),λ)

# Logistic
logistic(i::Integer,μ,s) = μ + s*log(omega_component(i)/(1-omega_component(i)))
logistic(μ,s) = logistic(genint(),μ,s)