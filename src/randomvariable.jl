abstract RandomVariable{T}
typealias RandVar{T} RandomVariable{T}

for finame in ["randomvariablesymbolic.jl",
#                "symbolic2.jl",
               "randomarray.jl",]
    include(joinpath("randomvariable", finame))
end
