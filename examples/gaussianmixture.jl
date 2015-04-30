using Sigma

## Mixture of Gaussians
# A mixture of Gaussians implemented using the ability of RandArrays to take
# Integer valued RandVars as indices
A = iid(Float64,i->normal(i,i,1/i),5)
w = categorical(pnormalize([20,2,3,4,20]))
mix = A[w]
samples = rand(mix, 1000)