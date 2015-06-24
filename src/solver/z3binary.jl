## Conversion of Sigma Function into Z3 expression
## ==================================================

type Z3BinaryRandVar{T} <: RandVar{T}
  dims::Set{Int}
  sexpr::SExpr
end

dims(X::Z3BinaryRandVar) = X.dims

function convert{T}(::Type{Z3BinaryRandVar{T}}, X::RandVar{T})
  Z3BinaryRandVar{T}(dims(X),convert(SExpr,X))
end

## Parsing Output of z3
## =======================
# Add extra SMT2 information to complete program
function headerfooter_z3(program::Vector{SExpr})
  SExpr[program...,
        SExpr("(check-sat)"),
        SExpr("(exit)")]
end

function check_z3(program::SExpr)
  # println("Check")
  # println(program.ex)
  fname = randstring()
  withext = "$fname.smt2"
  f = open(withext,"w")
  write(f,program.ex)
  close(f)
  satstatus = parse_sat_status(readall(`z3 $withext`))
  rm(withext)
  satstatus
end


# Will need to instantiate ω values
function call(X::Z3BinaryRandVar{Bool}, ω::AbstractOmega{Float64})
  # Generate Variable Names
  declares = SExpr[]
  for dim in dims(ω)
    push!(declares,SExpr("(declare-fun omega$dim () Real)"))
  end

  bounds = SExpr[]
  for dim in dims(ω)

    lb = SExpr("(assert (>= omega$dim $(dofmt(ω[dim].l))))")
    ub = SExpr("(assert (<= omega$dim $(dofmt(ω[dim].u))))")
    push!(bounds, lb)
    push!(bounds, ub)
  end

  pos_assertion = SExpr("(assert $(X.sexpr.ex))")
  program = vcat(declares, bounds, pos_assertion)
  full_program = headerfooter_z3(program)
  # Check both whether there exists a point which satisfies constraints
  pos_case = check_z3(merge(full_program))
  # println(merge(full_program).ex)

  neg_assertion = SExpr("(assert (not $(X.sexpr.ex)))")
  neg_program = vcat(declares, bounds, neg_assertion)
  full_neg_program = headerfooter_z3(neg_program)
  # And whether there exists a point which satisfies negation of constraints
  # println(merge(full_neg_program).ex)
  neg_case = check_z3(merge(full_neg_program))
  
  # If both are true, return {T,F}
  # @show pos_case
  # @show neg_case
  if pos_case & neg_case tf
  elseif pos_case t
  elseif neg_case f
  else
    error("Query or its negation must be true")
    println(merge(full_program).ex, "\n")
    println(merge(full_neg_program).ex)
  end
end
