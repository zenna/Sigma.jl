## Interface to dReal non-linear SMT solver
## ========================================

## Parsing Output of dReal (TODO: Interface directly through API)
## ==============================================================
parse_sat_status(satstatus::String) = ["sat" => SAT, "unsat" => UNSAT][strip(satstatus)]

# Parse a floatingpoint/integer from a string
numregex = "[-+]?[0-9]*\.?[0-9]+"
# Regex to extract variable assignments in model from dReal text output
modelregex = Regex("(\\w*) : \\[($numregex),\\s*($numregex)\\]")

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

function checksatdReal(program::SExpr)
  fname = randstring()
  withext = "$fname.smt2"
  @show withext
  f = open(withext,"w")
  write(f,program.e)
  close(f)
  satstatus = parse_sat_status(readall(`dReal -model $withext`))
  if satstatus == SAT
    @show "we got here"
    modelfile = open("$withext.model")
    model = parse_model_file(readlines(modelfile))
    close(modelfile)
    return satstatus, model
  else
    return satstatus, nothing
  end
end
