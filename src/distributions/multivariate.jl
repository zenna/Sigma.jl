## Multivariate Distributions
## ==========================

# dirichlet distribution
# Convert array of gammas to dirichlet Distribution
gammatodiriclet(x::PureRandArray) = x / sum(x)

function dirichlet(α::Vector{Float64})
  arr = RandVarAI{Float64}[gamma(α[i],1.0) for i = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

# Specify only omega component of first element of random array
function dirichlet(i::Int, α::Vector{Float64})
  arr = RandVarAI{Float64}[gamma(i+j-1,α[j],1.0) for j = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

# Specify all omega components
function dirichlet(is::Vector{Int}, α::Vector{Float64})
  @assert length(is) == length(α)
  arr = RandVarAI{Float64}[gamma(is[j],α[j],1.0) for j = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

## Independent Multivariates
## =========================
mvuniformai(a,b, i::Int, j::Int) = iid(Float64, c->uniformai(a,b),i,j)
mvuniformai(a,b, i::Int) = iid(Float64, c->uniformai(a,b),i)

mvnormalai(μ,σ, i::Int, j::Int) = iid(Float64, c->normalai(μ,σ),i,j)
mvnormalai(μ,σ, i::Int) = iid(Float64, c->normalai(μ,σ),i)
