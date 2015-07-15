## Elementary Rand Variables
## =========================

abstract ElementaryRandVar{T} <: SymbolicRandVar{T}
dims(X::ElementaryRandVar) = union([Set(X.dim), map(dims, args(X))...]...)::Set{Int}
has_single_dim(X::ElementaryRandVar) = true

## Continuous RandVars 
## ===================

immutable ArcSineRandVar{T <: Real, A <: SymbolicRandVar, B <: SymbolicRandVar} <: ElementaryRandVar{T}
  dim::Id
  a::A
  b::B
  ArcSineRandVar(dim::Id, a::SymbolicRandVar{Real}, b::SymbolicRandVar{Real}) = new(id,a,b)
end

"Uniformly distributed RandVar"
immutable UniformRandVar{T <: Real, A <:   Real} <: ElementaryRandVar{T}
  dim::Id
  lb::SymbolicRandVar{T}
  ub::SymbolicRandVar{T}
end

args(X::UniformRandVar) = @compat tuple(X.lb, X.ub)

"Normally distributed RandVar"
immutable NormalRandVar{T <: Real, A <: Real} <: ElementaryRandVar{T}
  dim::Id
  μ::SymbolicRandVar{T}
  σ::SymbolicRandVar{T}
end

args(X::NormalRandVar) = @compat tuple(X.μ, X.σ)

"Beta distributed RandVar"
immutable BetaRandVar{T <: Real, A <: Real} <: ElementaryRandVar{T}
  dim::Id
  α::SymbolicRandVar{A}
  β::SymbolicRandVar{A}
end

## Discrete Distritbuions
## ======================
"Poisson Distribution"
immutable PoissonRandVar{T <: Integer, A <: Real} <: ElementaryRandVar{T}
  dim::Id
  λ::SymbolicRandVar{A}
end

args(X::PoissonRandVar) = @compat tuple(X.λ)