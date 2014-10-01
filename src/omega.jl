# Omega is the sample space which random variables transform.
immutable Omega{T}
  intervals::Dict{Int64,T}
end

Omega() = Omega(Dict{Int64,Interval}())
Omega(::Type{EnvVar}) = Omega{EnvVar}(Dict{Int64, EnvVar}())

function getindex{T}(o::Omega{T}, key::Int64)
  if haskey(o.intervals,key)
    o.intervals[key]
  else
    i = unitinterval(T)
    o.intervals[key] = i
    i
  end
end

# REVIEW: add setindex(omega)
# REVIEW: CLEAN UP OMEGA TYPE MESS

measure(o::Omega) = prod([measure(i) for i in values(o.intervals)])
# measure(o::Omega{EnvVar}) = prod([measure(i) for i in values(o.intervals)])
# function measure(o::Omega)
#   prod([measure(i.worlds[noconstraints]) for i in values(o.intervals)])
# end
measure(os::Vector{Omega}) = [measure(o) for o in os]
measure{T}(os::Vector{Omega{T}}) = [measure(o) for o in os]
measure(os::Vector{Omega{EnvVar}}) = [measure(o) for o in os]


to_disj_intervals(b::Box) = [IntervalDisj(b.intervals[:,i]) for i = 1:num_dims(b)]

# REVIEW: IS THIS ORDERING THINGS CORRECTLY?
function middle_split(o::Omega)
  ks = collect(keys(o.intervals))
  vs = collect(values(o.intervals))
  box = convert(NDimBox,vs)
  z = middle_split(box)
  map(x->Omega(Dict(ks,to_intervals(x))),z)
end

# REVIEW: REMOVE OR ENABLE
# function middle_split(o::Omega{IntervalDisj})
#   ks = collect(keys(o.intervals))
#   vs = collect(values(o.intervals))
#   box = convert(NDimBox,vs)
#   z = middle_split(box)
#   map(x->Omega(Dict(ks,to_disj_intervals(x))),z)
# end

# function middle_split(o)
#   ks = collect(keys(o.intervals))
#   vs = map(x->x.worlds[noconstraints],collect(values(o.intervals)))
#   box = convert(NDimBox,vs)
#   boxes = middle_split(box)
#   map(x->Omega(Dict(ks,convert(Vector{EnvVar},x))),boxes)
# end

middle_split(os::Vector{Omega}) = map(middle_split, os)

function rand(o::Omega)
  s = Dict{Int64,Float64}()
  for interval in o.intervals
    s[interval[1]] = rand_interval(interval[2].l,interval[2].u)
  end
  SampleOmega(s)
end

immutable SampleOmega
  samples::Dict{Int64,Float64}
end
SampleOmega() = SampleOmega(Dict{Int64,Float64}())

function getindex(o::SampleOmega, key::Int64)
  if haskey(o.samples,key)
    o.samples[key]
  else
    i = rand()
    o.samples[key] = i
    i
  end
end

function convert(::Type{Vector{Box}}, os::Vector{Omega})
  map(x->convert(NDimBox,collect(values(x.intervals))),os)
end
