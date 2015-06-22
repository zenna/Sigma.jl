## Partitions of Sample Space Ω
## ============================

@doc """A partition of a set containing both an under approximation, and the rest
  The rest is an overapproximation - rest""" ->
type ApproxPartition{D<:Domain}
  under::Vector{D}
  rest::Vector{D}
end

@doc "Lower and upper bounds for measure of partition" ->
function measure(p::ApproxPartition)
  lb = isempty(p.under) ? 0 : sum([measure(event) for event in p.under])
  rest = isempty(p.rest) ? 0 : sum([measure(event) for event in p.rest])
  ub = lb + rest
  Interval(lb,ub)
end

## Sampling
## ========

@doc "A partition which is efficient for drawing many samples." ->
type SampleablePartition {D<:Domain}
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

@doc "Point sample from preimage - may be invalid point due to approximations" ->
abstract_sample(p::SampleablePartition) = p.over[rand(p.cat)]

@doc "`n` Point samples from preimage - may be invalid point due to approximations" ->
function point_sample(p::SampleablePartition, n::Integer)
  rand_indices = rand(p.cat, n)
  events = [p.over[i] for i in rand_indices]
  [rand(event) for event in events]
end

point_sample(p::SampleablePartition) = point_sample(p,1)[1]

@doc "Do refined rejection sampling from preimage" ->
function point_sample_exact(p::SampleablePartition, Y::RandVar{Bool}; maxtries = 1E7)
  for i = 1:maxtries
    sample = rand(p)
    if call(Y,sample) return sample end
  end
  #TODO: Better error handling
  error("Could not get sample in $maxtries tries")
end

