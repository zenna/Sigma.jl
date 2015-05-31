# uniform
uniform(i::Int,a::Real, b::Real) = (b-a)*omega_component(i) + a
uniform(a::Real, b::Real) = uniform(genint(), a,b)

# Bernoulli
flip(i::Int, p::Real) = p >= omega_component(i)
flip(i::Int) = 0.5 >= omega_component(i)
flip(p::Real) = flip(genint(), p)
flip() = flip(genint())

# Exponential
exponential(i::Int, λ::Real) = (-log(1-omega_component(i)))/λ
exponential(i::Int, λ::RandVar{Real}) = (-log(1-omega_component(i)))/λ