immutable SMTSolver
  template::Function #Adds solver specific SMT2 code e.g. header/foot
  checksat::Function #Calls the solver
end

immutable SExpr e::ASCIIString end

for finame in ["dreal.jl",
               "z3.jl"]
    include(joinpath("smtsolvers", finame))
end

string(s::SMTSolver) = [dreal3 => "dreal3", dreal => "dreal", z3 => "z3"][s]
print(io::IO, s::SMTSolver) = print(io, string(s))
show(io::IO, s::SMTSolver) = print(io, string(s))
showcompact(io::IO, s::SMTSolver) = print(io, string(s))
