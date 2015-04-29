## Measure
## =======
measure(b::HyperBox) = prod([b.intervals[2,i] - b.intervals[1,i] for i = 1:ndims(b)])
measure{B<:HyperBox}(bs::Vector{B}) = [measure(b) for b in bs]
logmeasure(b::HyperBox) = sum(map(log,[b.intervals[2,i] - b.intervals[1,i] for i = 1:ndims(b)]))

# measure{T}(b::LazyBox{Interval{T}}) = prod([measure(i) for i in values(o.intervals)])
# logmeasure{T}(b::LazyBox{Interval{T}}) = sum([log(measure(i)) for i in values(o.intervals)])
