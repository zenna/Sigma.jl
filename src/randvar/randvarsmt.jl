## Random Variables with SMT2 representation
## =========================================
# RandVarSMT creates a representation which can be directly sent to SMT2 solvers,
# such as dReal or Z3.
smt_counter = Counter(0)
genvar() = symbol("x$(inc(smt_counter))")

@doc "Basic types that can be expressed in SMT" ->
SMTPrim = Union(Symbol, String, Real, Expr)

@doc "A Random Variable representation for use with SMT solvers." ->
type RandVarSMT{T} <: RandVar{T}
  ast::SMTPrim
  asserts::Dict{Symbol, (DataType,SMTPrim)}
  assert_gens::Set{Function} # Generate dynamic asserts as function of Omega
  dims::Set{Int}
end

# function RandVarSMT(ast::SMTPrim,assert_gens::Set{Function},dims::Set{Int})
#   RandVarSMT{T}(ast,Dict(),assert_gens,dims)
# end

# Number of dimensions of Omega which it maps from
@doc "Number of dimensions of sample space that X transforms" ->
ndims(X::RandVarSMT) = length(X.dims)
ast(X::RandVarSMT) = X.ast

## Julia-SMT Compatibility
## =======================
@doc """Maps primitive Julia function x to smt2 symbol representation.
  e.g. juliat2smt(ifelse) = :ite""" ->
function julia2smt(x::Function)
  julia2smts =
  @compat Dict((&) => :and,
               (|) => :or,
               (!) => :not,
               (==) => :(=),
               (>) => :>,
               (>=) => :>=,
               (<) => :<,
               (<=) => :<=,
               isapprox => :isapprox,
               ifelse => :ite,
               (+) => :+,
               (-) => :-,
               (*) => :*,
               (/) => :/,
               abs => :abs)
  julia2smts[x]
end

function julia2smt(x::Symbol)
  julia2smts =
  @compat Dict(:(&) => :and,
               :(|) => :or,
               :(!) => :not,
               :(==) => :(=),
               :ifelse => :ite)
  haskey(julia2smts, x) ? julia2smts[x] : x
end

julia2smt{T<:Union(String,Real,Bool)}(x::T) = x
@compat julia2smt(x::DataType) = Dict(Float64 => :Real, Int => :Int, Bool => :Bool)[x]

## Conversion from Expr to SExpr
## ============================
# A string representation of an S-Expr
sexpr_parse(e) = string(julia2smt(e))
sexpr_parse(e::Expr) = convert(SExpr, e).e
combine(exprs::Vector{SExpr}) = SExpr(join([expr.e for expr in exprs],"\n"))

function convert(::Type{SExpr}, e::Expr)
  @assert e.head == :call "$(e.head), $e"
  expr_string = [sexpr_parse(a) for a in e.args]
  SExpr("($(join(expr_string, " ")))")
end

@doc "Convert a Boolean Random Variable into a vector of SExprs" ->
function assertions(X::RandVarSMT{Bool}, solver::SMTSolver,  ω)
  # Generate Dynamic Asserts
  sexprs = SExpr[]
  for gen in X.assert_gens
    [push!(sexprs, e) for e in gen(ω)]
  end

  static_declares = SExpr[]
  for (name, (RETURNT, assert_expr)) in X.asserts
    assert_e = convert(SExpr,:(assert((==)($name,$assert_expr))))
    declare_e = SExpr("(declare-fun $name () $(julia2smt(RETURNT)))")
    push!(static_declares, declare_e)
    push!(sexprs, assert_e)
  end

  # assert the random variable itelf
  push!(sexprs, convert(SExpr,:(assert($(X.ast)))))

  combine(solver.template(vcat(static_declares, sexprs)))
end

# (Mostly) To visualise the expression to be sent to solver
function convert(::Type{SExpr}, X::RandVarSMT{Bool}, ω; solver::SMTSolver = dreal3)
  assertions(X,solver, ω)
end

# Will need to instantiate ω values
function call(X::RandVarSMT{Bool}, ω::Omega{Float64}; solver::SMTSolver = z3, args...)
  # Generate Variable Names
  sexprs = SExpr[]
  for gen in X.assert_gens
    [push!(sexprs, e) for e in gen(ω)]
  end

  # Check both whether there exists a point which satisfies constraints
  program = assertions(X,solver,ω)
  existsatpoints = solver.checksat(program)

  # And whether there exists a point which satisfies negation of constraints
  negprogram = assertions(!X,solver,ω)
  existunsatpoints = solver.checksat(negprogram)

  # If both are true, return {T,F}
  if (existsatpoints == SAT) & (existunsatpoints == SAT) tf
  elseif existsatpoints == SAT t
  elseif existunsatpoints == SAT f
  else
    @show program.e
    @show negprogram.e
    error("Query or its negation must be true")
  end
end

## Dynamic Assertion Generators
## ============================
ω_nth(i::Int) = symbol("omega$i")

ω_asserts(i::Int,a::Real,b::Real) =
  [SExpr("(declare-fun $(ω_nth(i)) () Real)")
   SExpr("(assert (>= $(ω_nth(i)) $a))")
   SExpr("(assert (<= $(ω_nth(i)) $b))")]

ω_asserts(o::Omega{Float64}, i::Int) = ω_asserts(i,o[i].l,o[i].u)

@doc "Creates dynamic assertions for non-uniform distributions" ->
function other_asserts(o::Omega{Float64}, i::Int, name::Symbol, dist::Distribution,
                       RT::DataType)
  sexprs = SExpr[SExpr("(declare-fun $name () $(julia2smt(RT)))")]
  interval = o[i]
  quantile_l = quantile(dist, interval.l)
  quantile_u = quantile(dist, interval.u)
  !isinf(quantile_l) && push!(sexprs, SExpr("(assert (>= $name $quantile_l))"))
  !isinf(quantile_u) && push!(sexprs, SExpr("(assert (<= $name $quantile_u))"))
  sexprs
end

## RandVarSMT Algebra
## ==================
function combine(ast::Expr,RETURNT::DataType,randvars...)
  name = genvar()
  @compat new_assert = Dict(name=>(RETURNT, ast))
  # Combine with static asserts from all argument randvars
  arg_asserts = [X.asserts for X in randvars]
  all_asserts = merge(vcat(new_assert,arg_asserts)...)
  all_assert_gens = union([X.assert_gens for X in randvars]...)
  all_dims = union([X.dims for X in randvars]...)
  RandVarSMT{RETURNT}(name, all_asserts,
                      all_assert_gens,
                      all_dims)
end

@doc """
  Pointwise function lifting
  If `X` and `Y` are both random variables, `f(op,X,Y) = Z` where
  Z is a random variable defined as

  ```
  Z(ω) = X(ω) + Y(ω)
  ```
  """ ->
function lift(op,X::RandVarSMT,Y::RandVarSMT,RETURNT::DataType)
  newast = :($(julia2smt(op))($(ast(X)),$(ast(Y))))
  combine(newast,RETURNT,X,Y)
end

@doc "Lift op(X,c) where c is not RandVar" ->
function lift(op,X::RandVarSMT,c,RETURNT::DataType)
  newast = :($op($(ast(X)),$c))
  combine(newast,RETURNT,X)
end

@doc "Lift op(c,X) where c is not RandVar" ->
function lift(op,c,X::RandVarSMT,RETURNT::DataType)
  newast = :($op($c,$(ast(X))))
  combine(newast,RETURNT,X)
end

@doc "Unary Lift op(X)" ->
function lift(op,X::RandVarSMT,RETURNT::DataType)
  newast = :($op($(ast(X))))
  combine(newast,RETURNT,X)
end

# TODO: Get rid of other lifts, perf diff is minimal to 0
@doc """
  Pointwise Lifting - arbitrary arity
  This generalises the other lift methods, but is a litle slower.
  """ ->
function lift(op,RETURNT::DataType,args...)
  ast_args = Any[]
  randvar_args = RandVarSMT[]
  for arg in args
    if isa(arg,RandVarSMT)
      push!(ast_args, ast(arg))
      push!(randvar_args, arg)
    else
      push!(ast_args, arg)
    end
  end

  newast = Expr(:call, op, ast_args...)
  combine(newast,RETURNT,randvar_args...)
end

## Real × Real -> Real ##
for op = (:+, :-, :*, :/)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, Y::RandVarSMT{T2}) = lift($op,X,Y,promote_type(T1, T2))
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, c::T2) = lift($op,X,c,promote_type(T1, T2))
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarSMT{T2}) = lift($op,c,X,promote_type(T1, T2))
end

## Real -> Real ##
abs(X::RandVarSMT) = lift(X,Y)

## Real × Real -> Bool ##
for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, Y::RandVarSMT{T2}) = lift($op,X,Y,Bool)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarSMT{T1}, c::T2) = lift($op,X,c,Bool)
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarSMT{T2}) = lift($op,c,X,Bool)
end

## Real × Real -> Bool ##
for op = (:&, :|)
  @eval ($op)(X::RandVarSMT{Bool}, Y::RandVarSMT{Bool}) = lift($op,X,Y,Bool)
  @eval ($op)(X::RandVarSMT{Bool}, c::Bool) = lift($op,X,c,Bool)
  @eval ($op)(c::Bool, X::RandVarSMT{Bool}) = lift($op,c,X,Bool)
end

## Bool -> Bool ##
!(X::RandVarSMT{Bool})= lift(!,X,Bool)

# ## ifelse
ifelse{T}(A::RandVarSMT{Bool}, B::RandVarSMT{T}, C::RandVarSMT{T}) =
  lift(ifelse,T,A,B,C)

ifelse{T1<:Real}(A::RandVarSMT{Bool}, B::T1, C::T1) =
  lift(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarSMT{Bool}, B::RandVarSMT{T1}, C::T1) =
  lift(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarSMT{Bool}, B::T1, C::RandVarSMT{T1}) =
  lift(ifelse,T1,A,B,C)

## Printing
## ========
string(x::RandVarSMT{Bool}) = convert(SExpr, x, LazyOmega()).e
print(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
show(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
showcompact(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
