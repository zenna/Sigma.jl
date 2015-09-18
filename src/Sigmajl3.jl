using Docile
# call is in base in 0.4
export call
call(f::Function, x) = f(x)
juliadir = joinpath(homedir(),".julia","v0.3")
