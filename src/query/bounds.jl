## Queries using pre_bfs
## ====================
@doc "Lower and upper bounds for event under/overapproximated by sat/mixed sets" ->
function prob_bounds{T<:Domain}(satsets::Vector{T},mixedsets::Vector{T})
  lowerbound = sum(measure(satsets))
  upperbound = sum(measure(mixedsets)) + lowerbound
  Interval(lowerbound,upperbound)
end

@doc "Lower and upper bounds for the marginal probability of X" ->
function prob_bfs(X::RandVar{Bool}; pre_args...)
  satsets, mixedsets = pre_bfs(X, T, Omega(); pre_args...)
  prob_bounds(satsets, mixedsets)
end

@doc "Lower and upper bounds for the conditional probability of X given Y" ->
function cond_prob_bfs(X::RandVar{Bool}, Y::RandVar{Bool}; pre_args...)
  XYsatsets, XYmixedsets = pre_bfs(X & Y, T, Omega(); pre_args...)
  Ysatsets, Ymixedsets = pre_bfs(Y, T, Omega(); pre_args...)
  prob_bounds(XYsatsets, XYmixedsets) / prob_bounds(Ysatsets, Ymixedsets)
end
