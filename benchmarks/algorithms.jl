## Algorithms
## =======

# SMT Based
immutable SigmaSMT <: Algorithm
  capture::Vector{Symbol}
  randvartype::DataType
  preimage_sampler::Function
  ncores::Int
  split::Function
end

immutable SigmaRej <: Algorithm
  capture::Vector{Symbol}
end

immutable SigmaBFS <: Algorithm
  capture::Vector{Symbol}
end

immutable SigmaMH <: Algorithm
  capture::Vector{Symbol}
end

# eq_f{T}(x::T,y::T) = T.names == () ? (==) : deepequiv

# function deepequiv{T}(a::T,b::T)
#   for f in T.names
#     if Base.isdefined(a,f) && Base.isdefined(b,f)
#       same = eq_f(getfield(a,f), getfield(b,f))(getfield(a,f),getfield(b,f))
#       !same && return false
#     elseif Base.isdefined(a,f) $ Base.isdefined(b,f)
#       return false
#     end
#   end
#   return true
# end

# function deephash{T}(x::T, h = zero(Uint))
#   h += uint(0x7f53e68ceb575e76)
#   for t in T.names
#     if Base.isdefined(x,t)
#       h = hash(getfield(x,t),h)
#     end
#   end
#   return h
# end

# equiv{T}(a::T,b::T) =
#   all([getfield(a,f) == getfield(b,f) for f in T.names])

# # ==(a::SigmaAI,b::SigmaAI) = equiv(a,b)
# # hash(a::SigmaAI, h::Uint) = deephash(a,h)
# ==(a::SigmaSMT,b::SigmaSMT) = equiv(a,b)
# hash(a::SigmaSMT, h::Uint) = deephash(a,h)

# function isequal(a::SigmaSMT, b::SigmaSMT)
#
