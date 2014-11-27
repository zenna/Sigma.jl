# Abstract domains represent sets of finite values
abstract Domain{T}

for finame in ["bool.jl",
               "hyperbox.jl",
               "interval.jl",
               "simpledisjunctive.jl",
               "envvar.jl"]
    include(joinpath("domains", finame))
end
