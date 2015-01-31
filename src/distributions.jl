## Primitive Distributions
## =======================

typealias RV{T} Union(T, RandVar{T})

# random(i) = ω->ω[i]
random(i::Int64) = RandVarSymbolic(Float64, :(ω[$i]))


for finame in ["aiunivariate.jl",
               "aimultivariate.jl",
               "smtunivariate.jl",
               "smtmultivariate.jl",]
    include(joinpath("distributions", finame))
end

## Conventions
## ===========
# uniform = uniformai
# normal = normalai
# categorical = categoricalai
# geometric = geometricai
# poisson = poissonai
# discreteuniform = discreteuniformai
# gamma = gammaai
# betarv = betarvai
# flip = flipai

function aidistributions!()
  global uniform = uniformai
  global normal = normalai
  global categorical = categoricalai
  global geometric = geometricai
  global poisson = poissonai
  global discreteuniform = discreteuniformai
  global gamma = gammaai
  global betarv = betarvai
  global flip = flipai
  global mvuniform = mvuniformai
  global mvnormal = mvnormalai
  global iid = iidai
end

function smtdistributions!()
  global uniform = uniformsmt
  global normal = normalsmt
  global flip = flipsmt
  global mvuniform = mvuniformsmt
  global mvnormal = mvnormalsmt
  global iid = iidsmt
end

function metadistributions!()
  global uniform = uniformmeta
  global flip = flipmeta
  global mvuniform = mvuniformmeta
  global mvnormal = mvuniformmeta
end

aidistributions!() #Default to abstract interpretation
