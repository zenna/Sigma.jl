## Partitions of Sample Space Ω
## ============================

"""Approximate partition of a set: both an `under` approximation and `rest`.
`under ∪ rest` is an overapproximation of set."""
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

"`under ∪ rest` - over approximation"
collect{D}(p::ApproxPartition{D}) = vcat(p.under, p.rest)

## Sampling
## ========

"A partition which is efficient for drawing many samples"
type SampleablePartition{D<:Domain}
  over::Vector{D}
  last_under::Int
  cat::Categorical

  function SampleablePartition{D}(under::Vector, rest::Vector) where {D<:Domain}
    # Compute all measures and categorical weights only once
    over = vcat(under, rest)
    vols = Float64[measure(box) for box in over]
    pnormalize!(vols)
    cat = Categorical(vols, Distributions.NoArgCheck())
    new(over,length(over),cat)
  end
end

SampleablePartition{D}(p::ApproxPartition{D}) =
  SampleablePartition{D}(p.under, p.rest)

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
function point_sample_exact(p::SampleablePartition, Y::RandVar{Bool};
                            maxtries = 1E7)
  for i = 1:maxtries
    sample = rand(p)
    if Y(sample) return sample end
  end
  error("Could not get sample in $maxtries tries")
end

"Generic preimage partition interface - partition of Y^-1{true}."
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
