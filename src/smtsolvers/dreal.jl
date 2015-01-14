## Interface to dReal non-linear SMT solver
## ========================================

## Parsing Output of dReal
## =======================
parse_sat_status(satstatus::String) = ["sat" => SAT, "unsat" => UNSAT][strip(satstatus)]

# Parse a floatingpoint/integer from a string
numregex = "[-+]?[0-9]*\.?[0-9]+"
# Regex to extract variable assignments in model from dReal text output
modelregex = Regex("(\\w*) : \\[($numregex),\\s*($numregex)\\]")

# Add extra SMT2 information to complete program
function headerfooter(program::Vector{SExpr})
  SExpr[SExpr("(set-logic QF_NRA)"),
        program...,
        SExpr("(check-sat)"),
        SExpr("(exit)")]
end

function parse_model_file(model)
  # First line is "SAT with the following box"
  modeldict = Dict{String,Interval}()
  for linenum = 2:length(model)
    varline = strip(model[linenum])
    m = match(modelregex,varline)
    varname, lbound, ubound = m.captures
    modeldict[varname] = Interval(float(lbound), float(ubound))
  end
  modeldict
end

## Call solver command line
## ========================
function checksat(program::SExpr)
  fname = randstring()
  withext = "$fname.smt2"
  f = open(withext,"w")
  write(f,program.e)
  close(f)
  satstatus = parse_sat_status(readall(`dReal -model $withext`))
  rm(withext)
  if satstatus == SAT
    modelfile = open("$withext.model")
    model = parse_model_file(readlines(modelfile))
    close(modelfile)
    rm("$withext.model")
    return satstatus, model
  else
    return satstatus, nothing
  end
end

# The solver itself
const dreal = SMTSolver(headerfooter, checksat)
