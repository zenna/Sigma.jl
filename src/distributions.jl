## Primitive Distributions
## =======================
random(i) = ω->ω[i]

quantile{D <: Distribution}(d::D, X::RandomVariable) = ω->quantile(d, X(ω))
function quantile{D <: Distribution}(d::D, i::Interval)
  Interval(quantile(d,i.l),quantile(d,i.u))
end

# Distributions.jl Distribution -> RandomVariable by inverse transform sampling
randomize{D <: Distribution}(i, d::D) = quantile(d, random(i))

## Convenience Random Variable Constructors
normal(i,μ,σ) = randomize(i,Normal(μ,σ))
normal(μ,σ) = normal(genint(),μ, σ)
uniform(i,a,b) = randomize(i, Uniform(a,b))
uniform(a,b) = uniform(genint(),a,b)
chi(i,df) = randomize(i, Chi(df))
chi(df) = chi(genint(),df)
discreteuniform(i,a,b) = randomize(i,DiscreteUniform(a,b))
discreteuniform(a,b) = discreteuniform(genint(),a,b)
gamma(i,k,theta) = randomize(i,(Gamma(k,theta)))
gamma(k,theta) = gamma(genint(),k,theta)
categorical(i,weights) = randomize(i,(Categorical(weights)))
categorical(weights) = categorical(genint(),weights)
geometric(i,weight) =  randomize(i,(Geometric(weight)))
geometric(weight) =  geometric(genint(),weight)
poission(i,lambda) = randomize(i,Poisson(lambda))
poission(lambda) = poission(genint(), lambda)

prob(uniform(0,1) > 0.5)

flip(i) = 0.5 > random(i)
flip(i,p) = p > random(i)
