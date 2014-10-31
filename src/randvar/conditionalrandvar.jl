type ConditionalRandVar{T} <: RandVar{T}
  Ypre_overapprox::Vector
  c::Categorical
  X::RandVar{T}
  Y::RandVar{Bool}
end

function ConditionalRandVar{T}(Ypre_overapprox::Vector,X::RandVar{T},Y::RandVar{Bool})
  measures::Vector{Float64} = measure(Ypre_overapprox)
  pnormalize!(measures)
  c = Categorical(measures, Distributions.NoArgCheck())
  ConditionalRandVar{T}(Ypre_overapprox,c,X,Y)
end

function rand(C::ConditionalRandVar; maxtries = 1E7, countrejected = false)
  nrejected = 0
  ntried = 0
  while true
    omega = C.Ypre_overapprox[rand(C.c)]
    sample = rand(omega)
    if call(C.Y,sample)
      return countrejected ? (call(C.X,sample), nrejected) : call(C.X,sample)
    else
      nrejected = nrejected + 1
    end
    ntried += 1
    if ntried == maxtries
      return nothing
    end
  end
end
