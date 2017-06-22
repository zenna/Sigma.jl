"Breadth First Search Partition Algorithm"
immutable BFSPartition <: PartitionAlgorithm end

"Partitions by hierarhical decomposition of set using bread first search"
function pre_partition{D <: Domain}(
    Y::RandVar{Bool},
    init_box::D,
    ::Type{BFSPartition};
    precision::Float64 = default_precision(),
    dontstop::Function = loose_bounds,
    args...)

  under = Deque{D}()     # Partition of under approximation of Y-1({true})
  rest = Deque{D}()      # (Partition of over approximation of Y-1({true})) \ under
  push!(under, init_box)

  i = 0
  while dontstop(under, rest, i) && !isempty(under)
    lens(:partition_loop, i, under, rest)
    box = shift!(under)
    image = Y(box)

    # If all of the box is within preimage keep it
    if isequal(image,t) || issmall(box, precision)
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

## Stop Predicates
## ===============

"Is there enough memoery left?"
memory_left(under, rest, i; limit::Int = 1000) =
  length(under) + length(rest) < limit

"Have we exceeded the number of iterations?"
iters_left(under, rest, i; limit::Int = 1000) = i < limit

"True (i.e. continue) when lower and upper probability bounds are far"
function loose_bounds(under, rest, i; delta = 0.05, do_every_i::Int = 100)
  # For speed check only every do_every_i-th iteration
  if i % do_every_i == 0
    partition = ApproxPartition(collect(rest), collect(under))
    prob_bounds = measure(partition)
    return measure(prob_bounds) > delta
  else
    return true
  end
end

"Stops when precision is reached or time or memory constraints exhausted"
loose_bounds_limited(under, rest, i) =
  iters_left(under,rest,i) && memory_left(under, rest, i) && loose_bounds(under, rest, i)
