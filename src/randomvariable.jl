abstract RandomVariable

for finame in ["randomvariablesymbolic.jl",
               "randomarray.jl",]
    include(joinpath("randomvariable", finame))
end
