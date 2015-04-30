## Lebesgue Measure - Volume of box
## ================================
measure(b::Boxes) = prod([measure(b[dim]) for dim in dims(b)])
logmeasure(b::Boxes) = sum([log(measure(b[dim])) for dim in dims(b)])
measures{B<:Boxes}(bs::Vector{B}) = [measure(b) for b in bs]