## Elementary Rand Variables
## =========================

abstract ElementaryRandVar{T} <: SymbolicRandVar{T}
dims(X::ElementaryRandVar) = union([Set(X.dim), map(dims, args(X))...]...)::Set{Int}
has_single_dim(X::ElementaryRandVar) = true
num_params{T <: ElementaryRandVar}(X::Type{T}) = length(fieldnames(X)) - 1

abstract ClosedFormQuantileRandVar{T} <: ElementaryRandVar{T}

## Continuous RandVars 
## ===================Arcsine

immutable ArcsineRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  a::A
  b::B
  ArcSineRandVar{T<:Real}(dim::Id, a::SymbolicRandVar{T}, b::SymbolicRandVar{T}) = new{T, T, T}(id,a,b)
end

"Uniformly distributed RandVar"
immutable UniformRandVar{T <: Real, A <: Real, B <: Real} <: ClosedFormQuantileRandVar{T}
  dim::Id
  lb::SymbolicRandVar{A}
  ub::SymbolicRandVar{B}
end

quantile_expr(x::UniformRandVar) = (x.lb - x.ub) * omega_component(X.dim) + x.lb

args(X::UniformRandVar) = @compat tuple(X.lb, X.ub)

"Normally distributed RandVar"
immutable NormalRandVar{T <: Real, A <: Real, B <: Real} <: ElementaryRandVar{T}
  dim::Id
  μ::SymbolicRandVar{A}
  σ::SymbolicRandVar{B}
end

# param_types(X::Type{NormalRandVar}) = [Float64, Float64]

args(X::NormalRandVar) = @compat tuple(X.μ, X.σ)

"Beta distributed RandVar"
immutable BetaRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  α::A
  β::B
end

## Discrete Distritbuions
## ======================
"Bernoulli Distribution"
immutable BernoulliRandVar{Bool, P <: Real} <: ClosedFormQuantileRandVar{Bool}
  dim::Id
  p::SymbolicRandVar{P}
end

args(X::BernoulliRandVar) = tuple(X.p)
quantile_expr(X::BernoulliRandVar) = X.p >= omega_component(X.dim)


# FIXME: Closed form?
"Binomial RandVar"
immutable BinomialRandVar{T <: Integer, N <: Integer, P <: Real} <: ElementaryRandVar{T}
  dim::Id
  n::SymbolicRandVar{N}
  p::SymbolicRandVar{P}
end

args(X::BinomialRandVar) = tuple(X.n, X.p)

# "Categorical Distribution"
# immutable CategoricalRandVar{T <: Integer, p::}
# end

"Discrete Uniform RandVar"
immutable DiscreteUniformRandVar{T <: Integer, A <: Integer, B <: Integer} <: ElementaryRandVar{T}
  dim::Id
  a::SymbolicRandVar{A}
  b::SymbolicRandVar{B}
end

"Uniformly distributed RandVar"
immutable PoissonRandVar{T <: Real, A <: Real} <: ClosedFormQuantileRandVar{T}
  dim::Id
  λ::SymbolicRandVar{A}
end

# args(X::PoissonRandVar) = @compat tuple(X.λ)

# ClosedFormQuantileRandVar = Union(UniformRandVar)