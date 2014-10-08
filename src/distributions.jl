## Primitive Distributions
## =======================
random(i) = ω->ω[i]

# quantile(d::Normal, X::RandomVariable) = ω->quantile(d, X(ω))
quantile{D <: Distribution}(d::D, X::RandomVariable) = ω->quantile(d, X(ω))
function quantile{D <: Distribution}(d::D, i::Interval)
  Interval(quantile(d,i.l),quantile(d,i.u))
end

# Distributions.jl Distribution -> RandomVariable by inverse transform sampling
randomize{D <: Distribution}(i, d::D) = quantile(d, random(i))

## Convenience Random Variable Constructors
normal(i,μ,σ) = randomize(i,Normal(μ,σ))
uniform(i,a,b) = randomize(i, Uniform(a,b))
chi(i,df) = randomize(i, Chi(df))
discreteuniform(i,a,b) = randomize(i,DiscreteUniform(a,b))
gamma(i,k,theta) = randomize(i,(Gamma(k,theta)))
categorical(i,weights) = randomize(i,(Categorical(weights)))
geometric(i,weight) =  randomize(i,(Geometric(weight)))
poission(i,lambda) = randomize(i,Poisson(lambda))

flip(i) = 0.5 > random(i)
flip(i,p) = p > random(i)

A = poission(1,4)
B = discreteuniform(2,0,10)
plot_sample_cond_density(A+B,A>0,10000)