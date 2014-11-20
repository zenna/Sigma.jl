## Interface to dReal non-linear SMT solver
## ========================================

id(X::Var) = X.id
id(x::Int) = x
id(x::Real) = x
id(x::Bool) = x

isequal(X::Var, Y::Var) = X.id == Y.id && X.asserts == Y.asserts

# S-Expr in string form
immutable LispExpr e::ASCIIString end

declare(X::Var) = LispExpr("(declare-fun $(X.id) () $(rangetype(X))")

function asserts(X::Var)
  declareset = Set{LispExpr}()
  push!(declareset, declare(X))

  assertset = Set{LispExpr}()
  for a in X.asserts
    expandedargs = [id(arg) for arg in fargs(a)]
    argstring = join(expandedargs," ")
    push!(assertset, LispExpr("(assert ($(fsymbol(a)) $argstring)"))
  end
  declareset, assertset
end

# Defualt behaviour for non-Vars is to return empty list
asserts_recursive(X) = Set{LispExpr}(), Set{LispExpr}()

function asserts_recursive(X::Var)
  declareset, assertset = asserts(X)
  for a in X.asserts
    for arg in fargs(a)
      new_declareset, new_assertset = asserts_recursive(arg)
      declareset = union(declareset,new_declareset)
      assertset  = union(assertset, new_assertset)
    end
  end
  declareset, assertset
end

fsymbol(e::Expr) = e.args[1]
fargs(e::Expr) = e.args[2:end]



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

function checksat(program::String)
  fname = randstring()
  withext = "$fname.smt2"
  @show withext
  f = open(withext,"w")
  write(f,program)
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