using Sigma

Σ_1 = 2 * eye(5,5)
μ = MvNormal(zeros(5), Σ_1)
Σ_2 = eye(5,5)
Σ_prior = Wishart(5,Σ_2)
w = MvNormal(rand(μ), rand(Σ_prior))
x = [Uniform(-1,1) for j = 1:5, i = 1:500]
τ = Gamma(0.5,2)
ϵ = [Normal(0,1/rand(τ)) for i = 1:500]
y = [rand(w)' * rand(x[i,j]) + ϵ[i] for j=1:5, i = 1:500]

dist(w, y = x[])

# Nubmer of random variables is
num_rvs = 5*5 + 5*500 + 1 * 500
