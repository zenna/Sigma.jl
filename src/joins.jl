## Joins
⊔(x::Float64, y::Float64) = Interval(x,y)
⊔(x::Vector) = reduce(⊔,x)
