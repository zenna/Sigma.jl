## Elementary Rand Variables
## =========================

abstract ElementaryRandVar{T} <: SymbolicRandVar{T}
dims(X::ElementaryRandVar) = union([Set(X.dim), map(dims, args(X))...]...)::Set{Int}
has_single_dim(X::ElementaryRandVar) = true
num_params{T <: ElementaryRandVar}(X::Type{T}) = length(X.names) - 1

## Continuous RandVars 
## ===================Arcsine

immutable ArcsineRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  a::A
  b::B
  ArcSineRandVar(dim::Id, a::SymbolicRandVar{Real}, b::SymbolicRandVar{Real}) = new(id,a,b)
end

"Uniformly distributed RandVar"
immutable UniformRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  lb::A
  ub::B
end

quantile_expr(x::UniformRandVar) = (x.lb - x.ub) * omega_component(X.dim) + x.lb

args(X::UniformRandVar) = @compat tuple(X.lb, X.ub)

"Normally distributed RandVar"
immutable NormalRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  μ::A
  σ::B
end

args(X::NormalRandVar) = @compat tuple(X.μ, X.σ)

"Beta distributed RandVar"
immutable BetaRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  α::A
  β::B
end

## Discrete Distritbuions
## ======================
"Poisson Distribution"
immutable PoissonRandVar{T <: Integer, A <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  λ::A
end

args(X::PoissonRandVar) = @compat tuple(X.λ)

ClosedFormQuantileRandVar = Union(UniformRandVar)