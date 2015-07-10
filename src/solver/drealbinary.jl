## Conversion of Sigma Function into DReal expression
## ==================================================

typealias DimToVar Dict{Int,DReal.Ex}

"A Lisp SExpr"
immutable SExpr
  ex::String
end

type DRealBinaryRandVar{T} <: RandVar{T}
  dims::Set{Int}
  sexpr::SExpr
end

dims(X::DRealBinaryRandVar) = X.dims

for (name,op) in all_functional_randvars
  eval(
  quote
  function convert(::Type{SExpr}, X::$name)
    SExpr(string("(",julia2smt($op)," ",join([convert(SExpr,arg).ex for arg in args(X)], " ")..., ")"))
  end
  end)
end

function convert{T}(::Type{DRealBinaryRandVar{T}}, X::RandVar{T})
  DRealBinaryRandVar{T}(dims(X),convert(SExpr,X))
end

function julia2smt(x::Function)
  julia2smts =
  @compat Dict((&) => :and,
               (|) => :or,
               (!) => :not,
               (^) => :pow,
               (==) => :(=),
               ifelse => :ite)
  haskey(julia2smts, x) ? julia2smts[x] : x
end


convert(::Type{SExpr}, X::ConstantRandVar) = SExpr(string(X.val))
#add one for julia/c++ indexing mismatch, basically a HACK
convert(::Type{SExpr}, X::OmegaRandVar) = SExpr(string("omega",X.dim))


lambda_expr(X::RandVar) = Expr(:(->),:ω,convert(Expr,X))
lambda(X::RandVar) = eval(lambda_expr(X))


## Parsing Output of DReal
## =======================
function parse_sat_status(satstatus::String)
  # @show satstatus[1:20]
  # @show "delta-sat with delta"
  # @show satstatus
  if strip(satstatus) == "unsat"
    return false
  else
    return true
  end
end
#   Dict("sat" => SAT, "unsat" => UNSAT)[strip(satstatus)]
# end

# Parse a floatingpoint/integer from a string
numregex = "[-+]?[0-9]*\.?[0-9]+"
# Regex to extract variable assignments in model from DReal text output
modelregex = Regex("(\\w*) : \\[($numregex),\\s*($numregex)\\]")

# Add extra SMT2 information to complete program
function headerfooter(program::Vector{SExpr})
  SExpr[SExpr("(set-logic QF_NRA)"),
        program...,
        SExpr("(check-sat)"),
        SExpr("(exit)")]
end

## Call solver command line
## ========================
function check(program::SExpr)
  # println("Check")
  # println(program.ex)
  fname = randstring()
  withext = "$fname.smt2"
  f = open(withext,"w")
  write(f,program.ex)
  close(f)
  satstatus = parse_sat_status(readall(`DReal $withext`))
  rm(withext)
  satstatus
end

merge(sexprs::Vector{SExpr}) = SExpr(join([sexpr.ex for sexpr in sexprs], "\n"))

# Will need to instantiate ω values
function call(X::DRealBinaryRandVar{Bool}, ω::AbstractOmega{Float64})
  # Generate Variable Names
  declares = SExpr[]
  for dim in dims(ω)
    push!(declares,SExpr("(declare-fun omega$dim () Real)"))
  end

  bounds = SExpr[]
  for dim in dims(ω)

    lb = SExpr("(assert (>= omega$dim $(dofmt(ω[dim].l))))")
    ub = SExpr("(assert (<= omega$dim $(dofmt(ω[dim].u))))")

    # lb = SExpr("(assert (>= omega$dim $(ω[dim].l)))")
    # ub = SExpr("(assert (<= omega$dim $(ω[dim].u)))")
    push!(bounds, lb)
    push!(bounds, ub)
  end

  pos_assertion = SExpr("(assert $(X.sexpr.ex))")
  program = vcat(declares, bounds, pos_assertion)
  full_program = headerfooter(program)
  # Check both whether there exists a point which satisfies constraints
  pos_case = check(merge(full_program))
  # println(merge(full_program).ex)

  neg_assertion = SExpr("(assert (not $(X.sexpr.ex)))")
  neg_program = vcat(declares, bounds, neg_assertion)
  full_neg_program = headerfooter(neg_program)
  # And whether there exists a point which satisfies negation of constraints
  # println(merge(full_neg_program).ex)
  neg_case = check(merge(full_neg_program))
  
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

# # Returns an abstract bool
# function call(X::DRealRandVar{Bool},ω::AbstractOmega{Float64})
#   # 1. ∃ω ∈ A ∩ X : Does A contain any point X?
#   ctx = X.ctx
#   push_ctx!(ctx) #1
#   println("(push 1)")
#   for dim in dims(ω)
# #     @show dim
#     lb = (>=)(ctx,X.dimtovar[dim],ω[dim].l)
#     ub = (<=)(ctx,X.dimtovar[dim], ω[dim].u)
#     println("(assert",lb,")")
#     DReal.add!(ctx,lb)
#     println("(assert",ub,")")
#     DReal.add!(ctx,ub)
#   end
# #   push_ctx!(ctx) #2
#   println("(assert",X.ex,")")
#   DReal.add!(ctx, X.ex)
# #   println("About to check pop case")
#   println("(check-sat)")
#   pos_case = is_satisfiable(ctx)
# #   @show pos_case
#   println("(pop 1)")
#   pop_ctx!(ctx) #undo from 2 to here
# #   println("About to push")
#   println("(push 1)")
#   push_ctx!(ctx) #3
#   for dim in dims(ω)
# #     @show dim
#     lb = (>=)(ctx,X.dimtovar[dim],ω[dim].l)
#     ub = (<=)(ctx,X.dimtovar[dim],ω[dim].u)
#     println("(assert",lb,")")
#     DReal.add!(ctx,lb)
#     println("(assert",ub,")")
#     DReal.add!(ctx,ub)
#   end
# #   println("About to check neg case")
#   notex = (!)(ctx,X.ex)
#   println("(assert",notex,")")
#   DReal.add!(ctx, notex)

#   # 2. ∃ω ∈ A \ X : Does A contain any point not in X?
#   println("(check-sat)")
#   neg_case = is_satisfiable(ctx)
# #   @show pos_case
#   println("(pop 1)")
#   println("; end")
#   pop_ctx!(ctx) #roll back to 3
# #   pop_ctx!(ctx) #roll back to 1
#   if pos_case & neg_case tf
#   elseif pos_case t
#   elseif neg_case f
#   else
#     error("Query or its negation must be true")
#   end
# end
