"Stop after 10 iterations"
go_to_ten{T}(i::Int, history::Vector{Interval{T}}) = i < 10

"""Find values of `vars` such that `obj` is maximized or minimized.
  Assumes obj function is between `lb` and `ub`

  Optimizes by solving series questions of the form:
  Is there some model such that `cost` < `x`
  Uses binary search to efficiently find smallest `x` where the answer is true

  `obj`  - The cost value to be minimized (should be asserted to be a function of other variables)
  `lb`   - lower bound on cost
  `ub`   - upper bound on cost
  `dontstop` - boolean valued function determines when to continue optimization
"""
function minimize{T<:Real}(ctx::Context, obj::Ex{T}, vars::Ex...;
                          lb::T = typemin(T),
                          ub::T = typemax(T),
                          dontstop::Function = go_to_ten)
  @assert lb < ub "lower bound not less than upper bound"
  # Check its possible to get cost within specified bounds
  add!(ctx,(obj >= lb) & (obj <= ub))
  !is_satisfiable(ctx) && error("No model has objective value between $lb and $ub")

  local cost_bounds = Interval(lb,ub) # Bounds optimal cost
  local cost # best cost seen so far
  local optimal_model # best model (of vars) seen so far
  local last_test_issat # wheter last test was satisfiable
  history = Interval{T}[] # record history of cost_bounds intervals
  i = 0
  while dontstop(i, history)
    i += 1
    push_ctx!(ctx)

    # Test whether optimal cost is in upper or lower half of cost_bounds
    lhalf, uhalf = mid_split(cost_bounds)
    # current_lb, current_ub = uhalf.l, uhalf.u
    current_lb, current_ub = lhalf.l, lhalf.u
    add!(ctx,(obj >= current_lb) & (obj <= current_ub))

    println("checking")
    # if SAT, optimal cost is the lower half, split lower half next iteration
    if @show is_satisfiable(ctx)
      last_test_issat = true

      # Actually, we know that optimal cost must be less than the cost
      # found from the last test. Use that as an upper bound for effiency
      amodel = model(ctx,obj,vars...)
      cost = amodel[1]
      optimal_model = amodel[2:end]
      # cost_bounds = Interval(cost.l, current_ub)
      @show cost_bounds = Interval(current_lb, cost.u)
    else
      # Otherwise it must be in the upperhalf, split upper half next iteration
      last_test_issat = false
      # cost_bounds = lhalf
      @show  cost_bounds = uhalf
    end

    push!(history, cost_bounds)
    pop_ctx!(ctx)
  end

  if last_test_issat
    return cost, optimal_model
  else
    # If the last test returns UNSAT, we do not know what the best cost is
    # But we do have a best interval which must contain it
    push_ctx!(ctx)
    add!(ctx,(obj >= history[end].l) & (obj <= history[end].u))
    !is_satisfiable() && error("Should be satisfiable, cost must be within $(history[end])")
    amodel = model(ctx,obj,vars...)
    cost = amodel[1]
    optimal_model = amodel[2:end]
    pop_ctx!(ctx)
    return cost, optimal_model
  end
end

minimize(obj,vars::Ex...;args...) = minimize(global_context(), obj, vars...; args...)
