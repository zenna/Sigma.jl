## Partitions of Sample Space Ω
## ============================

"""A partition of a set containing both an under approximation, and the rest
  The rest is an overapproximation - rest"""
type ApproxPartition{D<:Domain}
  under::Vector{D}
  rest::Vector{D}
end

"Lower and upper bounds for measure of partition"
function measure(p::ApproxPartition)
  lb = isempty(p.under) ? 0 : sum([measure(event) for event in p.under])
  rest = isempty(p.rest) ? 0 : sum([measure(event) for event in p.rest])
  ub = lb + rest
  Interval(lb,ub)
end

"Get an over approximation"
collect{D}(p::ApproxPartition{D}) = vcat(p.under, p.rest)

## Sampling
## ========

"A partition which is efficient for drawing many samples."
type SampleablePartition{D<:Domain}
  over::Vector{D}
  last_under::Int
  cat::Categorical

  function SampleablePartition(under::Vector, rest::Vector)
    over = vcat(under, rest)
    vols = Float64[measure(box) for box in over]
    pnormalize!(vols)
    cat = Categorical(vols, Distributions.NoArgCheck())
    new(over,length(over),cat)
  end
end

SampleablePartition{D}(p::ApproxPartition{D}) = SampleablePartition{D}(p.under, p.rest)

"Point sample from preimage - may be invalid point due to approximations"
abstract_sample(p::SampleablePartition) = p.over[rand(p.cat)]

"`n` Point samples from preimage - may be invalid point due to approximations"
function point_sample(p::SampleablePartition, n::Integer)
  rand_indices = rand(p.cat, n)
  events = [p.over[i] for i in rand_indices]
  [rand(event) for event in events]
end

point_sample(p::SampleablePartition) = point_sample(p,1)[1]

"Do refined rejection sampling from preimage"
function point_sample_exact(p::SampleablePartition, Y::RandVar{Bool}; maxtries = 1E7)
  for i = 1:maxtries
    sample = rand(p)
    if call(Y,sample) return sample end
  end
  #TODO: Better error handling
  error("Could not get sample in $maxtries tries")
end

# Preimage of Y under F, unioned with X
function pre_partition{T}(
    Y::SymbolicRandVar{Bool},
    ::Type{T};
    RandVarType::Type = default_randvar(),
    precision = default_precision(),
    args...)

  init_box = unit_box(LazyBox{Float64}, dims(Y))
  Y_conv = convert(RandVarType{Bool}, Y)
  set_precision!(Y_conv, precision)
  pre_partition(Y_conv, init_box, T; precision=precision, args...)
end
