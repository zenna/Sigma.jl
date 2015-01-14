## Random Variables with SMT2 representation
## =========================================
# RandVarSMT creates a representation which can be directly sent to SMT2 solvers,
# such as dReal or Z3.

type RandVarSMT{T} <: RandVar{T}
  ast
  assert_gens::Set{Function} # Generate dynamic asserts as function of Omega
  dims::Set{Int}
end

# Number of dimensions of Omega which it maps from
ndims(X::RandVarSMT) = length(X.dims)
ast(X::RandVarSMT) = X.ast
gensmtsym(prefix::String) = symbol("$prefix$(genint())")

# A string representation of an S-Expr
sexpr_parse(e) = string(e)
sexpr_parse(e::Expr) = convert(SExpr, e).e
combine(exprs::Vector{SExpr}) = SExpr(join([expr.e for expr in exprs],"\n"))

function convert(::Type{SExpr}, e::Expr)
  @assert e.head == :call
  expr_string = [sexpr_parse(a) for a in e.args]
  SExpr("($(join(expr_string, " ")))")
end

# Will need to instantiate ω values
function call(X::RandVarSMT{Bool}, ω::Omega; solver::SMTSolver = z3)
  # Generate Variable Names
  sexprs = SExpr[]
  for gen in X.assert_gens
    [push!(sexprs, e) for e in gen(ω)]
  end

  # Check both whether there exists a point which satisfies constraints
  satcase = convert(SExpr,:(assert($(X.ast))))
  program = combine(solver.template([sexprs, satcase]))
  issatpoints = solver.checksat(program)

  # And whether there exists a point which satisfies negation of constraints
  unsatcase = convert(SExpr,:(assert(not($(X.ast)))))
  negprogram = combine(solver.template([sexprs, unsatcase]))
  isunsatpoints = solver.checksat(negprogram)

  # If both are true, return {T,F}
  if (issatpoints == SAT) & (isunsatpoints == SAT) TF
  elseif issatpoints == SAT T
  elseif isunsatpoints == SAT F
  else
    @show program.e
    @show negprogram.e
    error("Query or its negation must be true")
  end
end

ω_nth(i::Int) = symbol("omega$i")

## Dynamic Assertion Generators
## ============================
ω_asserts(i::Int,a::Real,b::Real) =
  [SExpr("(declare-fun $(ω_nth(i)) () Real)")
   SExpr("(assert (>= $(ω_nth(i)) $a))")
   SExpr("(assert (<= $(ω_nth(i)) $b))")]

ω_asserts(o::Omega, i::Int) = ω_asserts(i,o[i].l,o[i].u)

function distasserts(o::Omega, dim::Int, name::Symbol, dist::Distribution)
  error("notdone")
  interval = o[i]
  quantile_l = quantile(dist, interval.l)
  quantile_u = quantile(dist, interval.u)
#   [:(assert((>=)($name,$quantile_l))),
#    :(assert((<=)($name,$quantile_u)))]
end

## RandVarSMT Arithmetic
## =====================
# Binary functions, with Real output
for op = (:+, :-, :*, :/)
  @eval begin
    function ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, Y::RandVarSMT{T2})
      let op = $op
        RETURNT = promote_type(T1, T2)
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSMT{RETURNT}(newast, union(X.assert_gens, Y.assert_gens),
                            union(X.dims, Y.dims))
      end
    end
  end
end

# Real × Real -> Bool
for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval begin
    function ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, Y::RandVarSMT{T2})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSMT{Bool}(newast, union(X.assert_gens, Y.assert_gens),
                                 union(X.dims, Y.dims))
      end
    end
  end
end

## Distributions
## =============
uniformsmt(i::Int64,a::Real,b::Real) =
  RandVarSMT{Float64}(:(($b - $a) * $(ω_nth(i)) + $a),
             Set([ω->ω_asserts(ω,i)]),Set(i))

function normalsmt(i::Int64,μ::Real,σ::Real)
  name = gensmtsym("normal$i")
  RandVarSMT{Float64}(name,
             Set([ω->normalasserts(o,i,name,Normal(μ,σ))]),
             Set(i))
end
