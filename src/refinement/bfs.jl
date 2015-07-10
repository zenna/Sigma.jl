## Preimage refinement by breadth first search
## ===========================================

immutable BFSPartition <: PartitionAlgorithm end

# Preimage of Y under F, unioned with X
function pre_partition{D <: Domain}(Y::RandVar{Bool},
                                    init_box::D,
                                    ::Type{BFSPartition};
                                    precision::Float64 = DEFAULT_PREC,
                                    dontstop::Function = iters_left,
                                    args...)
  under = Deque{D}()     # Partition of under approximation of Y-1({true})
  rest = Deque{D}()      # (Partition of over approximation of Y-1({true})) \ under
  push!(under, init_box)

  i = 0
  while dontstop(under, rest, i) && !isempty(under)
    lens(:partition_loop, i, under, rest)
    box = shift!(under)
    image = call(Y, box)

    # If all of the box is within preimage keep it
    if isequal(image,t)
      push!(rest, box)

    # Otherwise split it into disjoint subsets and repeat for each part
    elseif isequal(image,tf)
      for child in mid_split(box)
        push!(under, child)
      end
    end
    i += 1
  end

  ApproxPartition{D}(collect(rest), collect(under))
end

## Stop Functons
## =============

memory_left(under, rest, i; limit::Int = 100000) = length(under) + length(rest) < limit
iters_left(under, rest, i; limit::Int = 1000) = i < limit