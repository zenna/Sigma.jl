type Counter
  X::Int64
end

GLOBAL_COUNTER = Counter(0)
inc(c::Counter) = c.X +=1
genint() = (inc(GLOBAL_COUNTER);GLOBAL_COUNTER.X-1)
genvar(prefix="x") = "$prefix$(genint())"
restart_counter!() = GLOBAL_COUNTER.X = 0
