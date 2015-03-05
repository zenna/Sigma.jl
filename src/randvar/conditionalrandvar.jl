@doc "A preimage representation efficient for sampling form"
type SamplePreimage
  both::Vector
  lastunderapprox::Int
  cat::Categorical

  function SamplePreimage(underapprox::Vector,overapprox::Vector)
    both = vcat(underapprox,overapprox)
    measures::Vector{Float64} = measure(both)
    pnormalize!(measures)
    c = Categorical(measures, Distributions.NoArgCheck())
    new(both,length(underapprox,c))
  end
end

@doc "Point sample from preimage - may be invalid point due to approximations" ->
function rand(P::SamplePreimage)
  omega = P.both[rand(P.cat)]
  sample = rand(omega)
end

@doc "Do refined rejection sampling from preimage" ->
function reject_sample(P::SamplePreimage, Y::RandVar{Bool}; maxtries = 1E7)
  nrejected = 0
  ntried = 0
  for i = 1:maxtries
    sample = rand(p)
    if call(Y,sample) return sample end
  end
  error("Could not get sample in $maxtries tries")
end

@doc "Point Sample the preimage" ->
function pre_sample_bfs(Y::RandVar{Bool}, n::Int; pre_args...)
  Ysatsets, Ymixedsets = pre_bfs(Y, T, Omega(); pre_args...)
  p = SamplePreimage(Ysatsets,Ymixedsets)
  samples = reject_sample(p,n)
end

@doc "Point Sample from X given Y" ->
function cond_sample_bfs(X::RandVar, Y::RandVar{Bool}, n::Int; pre_args...)
  [call(X,s) for s in pre_sample_bfs(Y,n;pre_args...)]
end

cond_sample_bfs(X::RandVar, Y::RandVar{Bool}; pre_args...) = cond_sample_bfs(X,Y,1;pre_args...)[1]
