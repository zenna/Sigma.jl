# uniform
uniform(i::Int,a::Real, b::Real) = (b-a)*omega_component(i) + a

# Bernoulli
flip(i::Int, p::Real) = p >= omega_component(i)
flip(i::Int) = 0.5 >= omega_component(i)

# Exponential
exponential(i::Int, λ::Real) = (-log(1-omega_component(i)))/λ
exponential(i::Int, λ::RandVar{Real}) = (-log(1-omega_component(i)))/λ