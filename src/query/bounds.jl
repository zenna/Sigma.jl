## Queries using pre_bfs
## ====================
function prob_bounds{T<:Domain}(satsets::Vector{T},mixedsets::Vector{T})
  lowerbound = sum(measure(satsets))
  upperbound = sum(measure(mixedsets)) + lowerbound
  Interval(lowerbound,upperbound)
end

function prob_bfs(X::RandVar{Bool}; box_budget = 1E3, max_iters = 1E3)
  satsets, mixedsets = pre_bfs(X, T, Omega(), box_budget = box_budget,
                                              max_iters = max_iters)
  prob_bounds(satsets, mixedsets)
end

function cond_prob_bfs(X::RandVar{Bool}, Y::RandVar{Bool};
                       box_budget = 1E3, max_iters = 1E3)
  XYsatsets, XYmixedsets = pre_bfs(X & Y, T, Omega(), box_budget = box_budget, max_iters = max_iters)
  Ysatsets, Ymixedsets = pre_bfs(Y, T, Omega(), box_budget = box_budget, max_iters = max_iters)
  prob_bounds(XYsatsets, XYmixedsets) / prob_bounds(Ysatsets, Ymixedsets)
end

function cond_bfs{E}(X::RandVar{E}, Y::RandVar{Bool}; box_budget = 1E3, max_iters = 1E3)
  Ysatsets, Ymixedsets = pre_bfs(Y, T, Omega(), box_budget = box_budget, max_iters = max_iters)
  ConditionalRandVar(vcat(Ymixedsets,Ysatsets), X,Y)
end