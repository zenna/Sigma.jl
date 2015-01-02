## Joins
⊔(x::Float64, y::Float64) = Interval(x,y)
⊔(x::Vector{Interval}) = reduce(⊔,x)
⊔(x::Vector) = reduce(⊔,x)
