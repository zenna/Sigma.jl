type ConditionalRandVar{T} <: RandVar{T}
  Ypre_overapprox::Vector
  c::Categorical
  X::RandVar{T}
  Y::RandVar{Bool}
end

function rand(C::ConditionalRandVar; maxtries = Inf, countrejected = false)
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