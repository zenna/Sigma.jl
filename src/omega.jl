  # Omega is the sample space which random variables transform.
immutable Omega{T} <: Domain{Float64}
  intervals::Dict{Int64,T}
end

Omega() = Omega(Dict{Int64,Interval}())
Omega(::Type{EnvVar}) = Omega{EnvVar}(Dict{Int64, EnvVar}())

function getindex{T}(o::Omega{T}, key::Int64)
  if haskey(o.intervals,key)
    o.intervals[key]
  else
    i = unitinterval()
    o.intervals[key] = i
    i
  end
end

setindex!{T}(o::Omega{T}, val::Interval, key::Int64) = o.intervals[key] = val

## Conversion
## ===========
convert(::Type{Vector{Interval}}, o::Omega) = collect(values(o.intervals))
convert{T}(::Type{Vector{Interval}}, o::Omega{T}, dims::Vector) = T[o[d] for d in dims]

function convert(::Type{Vector{HyperBox}}, os::Vector{Omega})
  map(x->convert(HyperBox,collect(values(x.intervals))),os)
end

# REVIEW: add setindex(omega)
# REVIEW: CLEAN UP OMEGA TYPE MESS
## Measure
## =======
measure(o::Omega) = prod([measure(i) for i in values(o.intervals)])
logmeasure(o::Omega) = sum([log(measure(i)) for i in values(o.intervals)])
measure{T}(os::Vector{Omega{T}}) = [measure(o) for o in os]

ndims(o::Omega) = length(keys(o.intervals))

## Split
## =====
function mid_split(o::Omega)
  ks = collect(keys(o.intervals))
  vs = collect(values(o.intervals))

  # Convert to hyperbox and split
  box = convert(HyperBox,vs)
  splits::Vector{HyperBox} = mid_split(box)

  # For each HyperBox in resulting split, convert to set of Intervals
  # Then recreate Omega using keys from parent.
  map(x->Omega(Dict(ks,convert(Vector{Interval},x))),splits)
end

# REMOVE REDUNDANC
function mid_partial_split(o::Omega, dims::Vector{Int})
  ks = collect(keys(o.intervals))
  vs = collect(values(o.intervals))

  # Mapping from omega key to order created using collect
  o_to_order = [ks[i] => i for i = 1:length(ks)]
  newdims = [o_to_order[dim] for dim in dims]

  # Convert to hyperbox and split
  box = convert(HyperBox,vs)
  splits::Vector{HyperBox} = mid_partial_split(box, newdims)

  # For each HyperBox in resulting split, convert to set of Intervals
  # Then recreate Omega using keys from parent.
  map(x->Omega(Dict(ks,convert(Vector{Interval},x))),splits)
end

mid_split(os::Vector{Omega}) = map(mid_split, os)

## Sampling
## ========
function rand(o::Omega)
  s = Dict{Int64,Float64}()
  for interval in o.intervals
    s[interval[1]] = rand_interval(interval[2].l,interval[2].u)
  end
  SampleOmega(s)
end

## Sample Omega
## ============
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


