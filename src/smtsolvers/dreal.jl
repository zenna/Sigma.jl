## Interface to dReal non-linear SMT solver
## ========================================

type DRealSolver <: SMTSolver
  ctx::dReal.Context
  rv2ex::Dict{RandVarMM, dReal.Ex}
  sample_space::Dict{Int,dReal.Ex}
end

dreal_val = DRealSolver(dReal.Context(qf_nra), Dict(),Dict())
global_dreal() = (global dreal_val; dreal_val)

# Generate dReal Ex values
function gen_expressions!(d::DRealSolver, X::RandVarMM)
  # Check which dimensions this random variable has
  for dim in dims(X)
    if dim ∉ keys(d.sample_space)
      d.sample_space[dim] = Var(d.ctx, Float64, "omega$dim",0.0,1.0)
    end
  end

  # TODO - STOP RECREATING EXPRESSION EVERY ITERATION
  if !haskey(d.rv2ex,X)
    @show "NEVER SEEN IT"
    (d.rv2ex[X] = expand(X, d.sample_space, d.ctx))
  else
    @show "Seen it before"
  end
  d.rv2ex[X], d.sample_space
  # expand(X, d.sample_space, d.ctx) , d.sample_space
end

expand(X, sample_space::Dict{Int,dReal.Ex}, ctx::Context) = X

function expand{T2}(X::RandVarMM{T2}, sample_space::Dict{Int,Ex}, ctx::Context)
  if israndomega(X)
    sample_space[randomegadim(X)]
  else
    eval(Expr(:call,func(X),ctx,[expand(arg, sample_space, ctx) for arg in args(X)]...))
  end
end

function call(d::DRealSolver, X::RandVarMM, ω::Omega{Float64})
  predicate, sample_space = gen_expressions!(d, X)
  ctx = d.ctx

  # Add Omega bounds
  @show "Got here"

  push_ctx!(ctx)
  for dim in dims(X)
    add!(ctx, (>=)(ctx,sample_space[dim],ω[dim].l))
    add!(ctx, (<=)(ctx,sample_space[dim],ω[dim].u))
  end
  @show "Got here2"

  # print(predicate)
  add!(ctx, predicate)
  overlap = is_satisfiable(ctx)
  pop_ctx!(ctx)
  @show "Got here3"

  # Negation
  push_ctx!(ctx)
  for dim in dims(X)
    add!(ctx, (>=)(ctx,sample_space[dim],ω[dim].l))
    add!(ctx, (<=)(ctx,sample_space[dim],ω[dim].u))
  end
  @show "Got here4"
  # print((!)(ctx,predicate))
  add!(ctx, (!)(ctx,predicate))
  space = is_satisfiable(ctx)
  pop_ctx!(ctx)

  @show "Got here5"
  # If both are true, return {T,F}
  if overlap & space  tf
  elseif overlap t
  elseif space f
  else
    print(predicate)
    print((!)(ctx,predicate))
    error("Query or its negation must be true")
  end
end

# immutable SExp

# ## Parsing Output of dReal
# ## =======================
# @compat parse_sat_status(satstatus::String) =
#   Dict("sat" => SAT, "unsat" => UNSAT)[strip(satstatus)]

# # Parse a floatingpoint/integer from a string
# numregex = "[-+]?[0-9]*\.?[0-9]+"
# # Regex to extract variable assignments in model from dReal text output
# modelregex = Regex("(\\w*) : \\[($numregex),\\s*($numregex)\\]")

# # Add extra SMT2 information to complete program
# function headerfooter(program::Vector{SExpr})
#   SExpr[SExpr("(set-logic QF_NRA)"),
#         program...,
#         SExpr("(check-sat)"),
#         SExpr("(exit)")]
# end

# function parse_model_file(model)
#   # First line is "SAT with the following box"
#   modeldict = Dict{String,Interval}()
#   for linenum = 2:length(model)
#     varline = strip(model[linenum])
#     m = match(modelregex,varline)
#     varname, lbound, ubound = m.captures
#     modeldict[varname] = Interval(float(lbound), float(ubound))
#   end
#   modeldict
# end

# ## Call solver command line
# ## ========================
# function checksat(program::SExpr)
#   fname = randstring()
#   withext = "$fname.smt2"
#   f = open(withext,"w")
#   write(f,program.e)
#   close(f)
#   satstatus = parse_sat_status(readall(`dReal $withext`))
#   rm(withext)
#   satstatus
# end

# function checksat_nra(program::SExpr)
#   fname = randstring()
#   withext = "$fname.smt2"
#   f = open(withext,"w")
#   write(f,program.e)
#   close(f)
#   satstatus = parse_sat_status(readall(`dReal3 $withext`))
#   rm(withext)
#   satstatus
# end

# function checksat_with_model(program::SExpr)
#   fname = randstring()
#   withext = "$fname.smt2"
#   f = open(withext,"w")
#   write(f,program.e)
#   close(f)
#   satstatus = parse_sat_status(readall(`dReal -model $withext`))
#   rm(withext)
#   if satstatus == SAT
#     modelfile = open("$withext.model")
#     model = parse_model_file(readlines(modelfile))
#     close(modelfile)
#     rm("$withext.model")
#     return satstatus, model
#   else
#     return satstatus, nothing
#   end
# end

# # The solver itself
# const dreal = SMTSolver(headerfooter, checksat)
# const dreal3 = SMTSolver(headerfooter, checksat_nra)
