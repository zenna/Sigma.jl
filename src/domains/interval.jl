## Quantile Functions
## ==================

"Computes quantile of interval, quantile is monotonic function so its easy"
function quantile{T}(X::Distributions.Distribution, p::Interval{T})
  # Quantiles must be between 0 and 1
  p_valid = intersect(p, unit(p))
  lb = quantile(X, p_valid.l)
  ub = quantile(X, p_valid.u)
  Interval{T}(lb, ub)
end

# quantile(X::Distributions.Distribution, i::Id, ω::Omega) = quantile(X, ω[i])

"Quantile when μ, σ and p are all intervals. This may not be correct."
function quantile{T}(::Type{Normal}, μ::Interval{T}, σ::Interval{T}, p::Interval{T})
  # FIXME, Float specific and feels a bit hacky.
  σ_valid = intersect(σ, Interval{T}(nextfloat(zero(T)), inf(T)))
  p_valid = intersect(p, unit(p))
  lb = quantile(Normal(μ.l, σ_valid.u), p_valid.l)
  ub = quantile(Normal(μ.u, σ_valid.l), p_valid.u)
  Interval{T}(lb, ub)
end

# Lebesgue Measure
measure(i::Interval) = i.u - i.l