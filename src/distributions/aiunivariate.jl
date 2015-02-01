## Abstract Interpretation Univariate Primitive Distribution
## =========================================================

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

# Categorical
categoricalai(i::Int64,weights::Vector{Float64}) =
  RandVarSymbolic(Int64,:(quantile(Categorical($weights),ω[$i])))

# function solve_quantile_argmin()
#   for j = 1:n
#     m = Model()

#     # Weights must be between 0 and 1
#     @defVar(m, 0 <= x[1:n] <= 1)

#     # Weights are constrained by weight parameter
#     for i = 1:n
#       @addConstraint(m, weights[i].l <= x[i] <= weights[i].u)
#     end

#     # Weights must sum to 1
#     @addConstraint(m, sum{x[i], i = 1:n} == 1)

#     @addConstraint(m, sum{x[i], i = 1:j} >= p.l)
#     status = solve(m)
#     if status == :Optimal
#       println(getValue(x))
#       return j
#     elseif status != :Infeasible
#       errror("status: $status unexpected")
#     end
#   end
# end

# function quantile_categorical(weights::Vector{Interval}, p::Interval)
#   # Find min
#   n = length(weights)
#   local b_l
# end

quantile_categorical(weights::Vector{Float64}, p::Float64) =
  quantile(Categorical(weights), p)

categoricalai{T<:Real}(i::Int64, weights::RandArray{T}) =
  RandVarSymbolic(Int, :(quantile_categorical(call($weights,ω), ω[$i])))

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

