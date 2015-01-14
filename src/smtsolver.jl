immutable SMTSolver
  template::Function #Adds solver specific SMT2 code e.g. header/foot
  checksat::Function #Calls the solver
end

immutable SExpr e::ASCIIString end

for finame in ["dreal.jl",
               "z3.jl"]
    include(joinpath("smtsolvers", finame))
end