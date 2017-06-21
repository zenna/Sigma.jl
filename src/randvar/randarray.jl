import Base.dot

"""An array of random variables (and also a random variable itself)
  `T` is the range type of elements (e.g for multivariate normal, T = Float64)
  `N` is the dimensionality of array"""
RandArray{T, N} = Array{T, N} where {T<:RandVar}
Smelly{Q} = Array{T, 1} where {T<:RandVar{Q}} where Q
ExecutableRandArray{T, N} = Array{T, N} where {T<:ExecutableRandVar}

dot(a::RandVar, b::RandVar) = a * b
dot(a::Number, b::RandVar) = a * b
dot(a::RandVar, b::Number) = a * b

convert{T}(::Type{ExecutableRandArray}, xs::Array{RandVar{T}}) =
  (rv -> convert(ExecutableRandVar{T}, rv)).(xs)

(xs::ExecutableRandArray)(ω::Omega) = (x->x(ω)).(xs)

rand(xs::RandArray) = xs(LazyRandomVector(Float64))

"Sample from `xs` conditioned on `y`"
function rand(xs::ExecutableRandArray,
              y::RandVar{Bool},
              n::Integer,
              preimage_sampler::Function = point_sample_mc;
              args...)
  preimage_samples = preimage_sampler(y, n; args...)
  [xs(sample) for sample in preimage_samples]
end

function rand(xs::RandArray,
              y::RandVar{Bool},
              n::Integer,
              preimage_sampler::Function = point_sample_mc;
              args...)
  executable_xs = convert(ExecutableRandArray, xs)
  rand(executable_xs, y, n; args...)
end

"Generate a sample from a rand array `xs` conditioned on `y`"
rand(xs::RandArray, y::RandVar{Bool}; args...) =  rand(xs, y, 1; args...)[1]
