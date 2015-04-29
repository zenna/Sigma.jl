# Inverse CDF for an interval
function quantile{D <: Distribution}(d::D, i::Interval)
  Interval(quantile(d,i.l),quantile(d,i.u))
end

# Lebesgue Measure
measure(i::Interval) = i.u - i.l
