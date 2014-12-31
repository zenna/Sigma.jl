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

normalai(i::Int64,μ::Real,σ::Real) =
  RandVarSymbolic(Float64,:(quantile(Normal($μ,$σ),ω[$i])))
normalai{T1<:Real, T2<:Real}(i::Int64,μ::RV{T1},σ::RV{T2})= (normalai(i,0.,1.) * σ) + μ
normalai(μ,σ) = normalai(genint(),μ, σ)

# uniform
uniformai(i::Int64,a::Real,b::Real) =
  RandVarSymbolic(Float64,:(quantile(Uniform($a,$b),ω[$i])))
uniformai{T1<:Real, T2<:Real}(i::Int64,a::RV{T1},b::RV{T2}) = (b - a) * uniformai(i,0.,1.) + a
uniformai(a,b) = uniformai(genint(),a,b)

# Bernoulli
flipai{T<:Real}(i::Int,p::RV{T}) = p > random(i)
flipai(i::Int64) = 0.5 > random(i)
flipai{T<:Real}(p::RV{T}) = p > random(genint())
flipai() = 0.5 > random(genint())

# Discrete Uniform
discreteuniformai(i::Int64,a::Int64,b::Int64) =
  RandVarSymbolic(Int64,:(quantile(DiscreteUniform($a,$b),ω[$i])))
discreteuniformai(i::Int64,a::RV{Int64},b::RV{Int64}) =
  (b - a) * discreteuniformai(i,0,1) + a
discreteuniformai(a,b) = discreteuniformai(genint(),a,b)

## Not Location Scale
## =================

gammaai(i::Int64,k::Float64,theta::Float64) =
  RandVarSymbolic(Float64,:(quantile(Gamma($k,$theta),ω[$i])))
gammaai(k,theta) = gammaai(genint(),k,theta)

betarvai(i::Int64,a::Float64,b::Float64) =
  RandVarSymbolic(Float64,:(quantile(Beta($a,$b),ω[$i])))
betarvai(a,b) = betarvai(genint(),a,b)

categoricalai(i::Int64,weights::Vector{Float64}) =
  RandVarSymbolic(Float64,:(quantile(Categorical($weights),ω[$i])))
categoricalai(weights) = categoricalai(genint(),weights)

geometricai(i::Int64,weight::Float64) =
  RandVarSymbolic(Int64,:(quantile(Geometric($weight),ω[$i])))
geometricai(weight) =  geometricai(genint(), weight)

quantile_geometric(weight::Float64, p::Float64) = quantile(Geometric(weight), p)
quantile_geometric(weight::Interval, p::Interval) =
  Interval(quantile(Geometric(weight.u),p.l), quantile(Geometric(weight.l),p.u))
geometricai(i::Int, weight::RandVar{Float64}) =
  RandVarSymbolic(Int, :(quantile_geometric(call($weight,ω), ω[$i])))

poissonai(i::Int64,lambda::Float64) =
  RandVarSymbolic(Int64,:(quantile(Poisson($lambda),ω[$i])))
poissonai(lambda) = poissonai(genint(), lambda)

## Multivariabe Distributions
## ==========================

# dirichlet distribution
# Convert array of gammas to dirichlet Distribution
gammatodiriclet(x::PureRandArray) = x / sum(x)

function dirichlet(α::Vector{Float64})
  arr = RandVarSymbolic{Float64}[gamma(α[i],1.0) for i = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

# Specify only omega component of first element of random array
function dirichlet(i::Int, α::Vector{Float64})
  arr = RandVarSymbolic{Float64}[gamma(i+j-1,α[j],1.0) for j = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

# Specify all omega components
function dirichlet(is::Vector{Int}, α::Vector{Float64})
  @assert length(is) == length(α)
  arr = RandVarSymbolic{Float64}[gamma(is[j],α[j],1.0) for j = 1:length(α)]
  gammatodiriclet(PureRandArray(arr))
end

## SMT Primitive Distributions
## ===========================
uniformsmt(i::Int64,a::Real,b::Real) =
  RandVarSMT{Float64}(:(($b - $a) * $(ω_nth(i)) + $a),
             Set([ω->ω_asserts(ω,i)]),Set(i))

function normalsmt(i::Int64,μ::Real,σ::Real)
  name = gensmtsym("normal$i")
  RandVarSMT{Float64}(name,
             Set([ω->normalasserts(o,i,name,Normal(μ,σ))]),
             Set(i))
end

function flipsmt(i::Int64, p::Real)
  @assert 0 <= p <= 1
  RandVarSMT{Bool}(:((>=)($(ω_nth(i)),$p)),
                   Set([ω->ω_asserts(ω,i)]),
                   Set(i))
end

flipsmt(p::Real) = flipsmt(genint(), p)
flipsmt(i::Int) = flipsmt(i,0.5)
flipsmt() = flipsmt(genint(),0.5)

## Conventions
## ===========

uniform = uniformai
normal = normalai
categorical = categoricalai
geometric = geometricai
poisson = poissonai
discreteuniform = discreteuniformai
gamma = gammaai
betarv = betarvai

uniform = uniformai
normal = normalai
flip = flipai
