function update_approx!(f, X, Y, satsets, mixedsets)
  children = mid_split(X)
  for child in children
    childsatstatus = checksat(f,Y,child)
    if childsatstatus == SAT
      push!(satsets,child)
    elseif childsatstatus == PARTIALSAT
      push!(mixedsets,child)
    end
  end
end

# Preimage of Y under F, unioned with X
#FIXME: Assumes X is PARTIALSAT
function pre_bfs{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5,
                                                     max_iters = 1E3)
  # Over and under approximation
  satsets = D[]
  local mixedsets
  satstatus = checksat(f,Y,X)
  if satstatus == SAT return D[X],D[]
  elseif satstatus == UNSAT return D[],D[]
  else mixedsets = D[X]
  end

  # debug
  ratios1 = Float64[]
  ratios2 = Float64[]

  # max iters is a hack to stop when we get very refined preimage
  # and we're no longer adding to our box_budget (just shrinking it)
  i = 0
  while length(mixedsets) + length(satsets) <= box_budget &&
        length(mixedsets) > 0 && i < max_iters

    # debug
    if i % 200 == 0
      push!(ratios1, length(mixedsets))
      push!(ratios2, length(satsets  ))
    end

#     println("Iteration $i : $length(boxes) boxes")
    Xsub = shift!(mixedsets)
    update_approx!(f,Xsub,Y,satsets,mixedsets)
    i += 1
  end

  if i == max_iters println("Reached Max iterations - $i")
  else println("Did $i iterations - max not reached") end
  satsets,mixedsets,ratios1,ratios2
end
