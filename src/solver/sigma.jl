## IBEX
## ====

typealias VarSet Set{IBEX.ExprSymbol}
typealias Visited Dict{RandVar,Any}
# Maps a variable to its interval domain
typealias DomainMap Dict{IBEX.ExprSymbol, Interval}


"Maps between Boolean Variable to a constraint: e.g. X => a+b>c"
typealias ConstraintMap Dict{Tuple{IBEX.ExprCtr,VarSet}, BoolVar}

type BoolCounter
  x::Int
end
inc!(x::BoolCounter) = x.x += 1
nextvar!(x::BoolCounter) = (y = x.x; inc!(x); y)

"Maps a predicate RandVar `X` to a ConstraintMap and a CMCNF of boolean structure"
function analyze(X::RandVar{Bool})
  ω = IBEX.ExprSymbol(maximum(dims(X))+1) # Ibex representation of sample space
  cmap = ConstraintMap() # map from ibex constraints to boolean variables
  cnf = CMCNF() # boolean cnf extracted
  aux_vars = Set{IBEX.ExprSymbol}() # Auxilary Variables
  next_boolvar = BoolCounter(0)
  visited = Dict{RandVar,Any}() # Visited Rand Vars and what they return

  result::BoolVar = expand(cmap,cnf,ω,aux_vars,visited,next_boolvar,X,args(X)...)

  println("aux_Vars are", aux_vars)
  push!(cnf,CMClause([CMLit(result,false)])) # Assert that the random variables should be true
  cmap, cnf, ω, aux_vars
end

#Default dict behaviour for constraint map
function add_constraint!(cmap::ConstraintMap, ctr::IBEX.ExprCtr, varset::VarSet, bc::BoolCounter)
  # Don't recreate if the constraint already exists
  if haskey(cmap,(ctr,varset))
    cmap[(ctr,varset)]
  else
    boolvar = nextvar!(bc)
    cmap[(ctr,varset)] = boolvar
    boolvar
  end
end

## Generic
## =======

# Unary
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::RandVar, a::RandVar)
  op_a = haskey(visited,a) ? visited[a] : (visited[a] =
    expand(cmap, cnf, ω, varset, visited, bc, a, args(a)...))
  expand(cmap, cnf, ω, varset,visited, bc, X, op_a)
end

# Binary
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::RandVar, a::RandVar, b::RandVar)
  op_a = haskey(visited,a) ? visited[a] : (visited[a] =
    expand(cmap, cnf, ω, varset, visited, bc, a, args(a)...))
  op_b = haskey(visited,b) ? visited[b] : (visited[b] =
    expand(cmap, cnf, ω, varset, visited, bc, b, args(b)...))
  expand(cmap, cnf, ω, varset,visited, bc, X, op_a, op_b)
end

# Ternary
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::RandVar,
                a::RandVar, b::RandVar, c::RandVar)
  op_a = haskey(visited,a) ? visited[a] : (visited[a] =
    expand(cmap, cnf, ω, varset, visited, bc, a, args(a)...))
  op_b = haskey(visited,b) ? visited[b] : (visited[b] =
    expand(cmap, cnf, ω, varset, visited, bc, b, args(b)...))
  op_c = haskey(visited,c) ? visited[c] : (visited[c] =
    expand(cmap, cnf, ω, varset, visited, bc, c, args(c)...))
  expand(cmap, cnf, ω, varset,visited, bc, X, op_a, op_b, op_c)
end

# Omega
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::OmegaRandVar)
  ω[X.dim]
end

# Constant
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::ConstantRandVar)
  retvalue = IBEX.ExprConstant(X.val)
  retvalue
end

# Generic Randvar{Bool} expand
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::RandVar{Bool}, a::RandVar{Bool}, b::RandVar{Bool})
  op_a = haskey(visited,a) ? visited[a] : (visited[a] =
    expand(cmap, cnf, ω, varset, visited, bc, a, args(a)...))
  op_b = haskey(visited,b) ? visited[b] : (visited[b] =
    expand(cmap, cnf, ω, varset, visited, bc, b, args(b)...))
  expand(cmap, cnf, ω, varset, visited, bc, X, op_a, op_b)
end

## Logical functions through Tseitin Transformation
## ================================================

# Or
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol, varset::VarSet, visited, bc::BoolCounter, X::OrRandVar, A::BoolVar, B::BoolVar)
  C = nextvar!(bc)
  # auxilary variable C = A | B
  # (A ∨ B ∨ !C) ∧ (!A ∨ C) ∧ (!B ∨ C)
  or_subcnf = CMCNF([CMClause([CMLit(A,false),CMLit(B,false),CMLit(C,true)]),
                     CMClause([CMLit(A,true),CMLit(C,false)]),
                     CMClause([CMLit(B,true),CMLit(C,false)])])
  push!(cnf, or_subcnf)
  C
end

# And
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol, varset::VarSet, visited, bc::BoolCounter, X::AndRandVar, A::BoolVar, B::BoolVar)
  C = nextvar!(bc)
  # auxilary variable C = A & B
  # (!A ∨ !B ∨ C) ∧ (A ∨ !C) ∧ (B ∨ !C)
  and_subcnf = CMCNF([CMClause([CMLit(A,true),CMLit(B,true),CMLit(C,false)]),
                      CMClause([CMLit(A,false),CMLit(C,true)]),
                      CMClause([CMLit(B,false),CMLit(C,true)])])
  push!(cnf, and_subcnf)
  C
end

# Biconditional (If and Only If)
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol, varset::VarSet, visited, bc::BoolCounter, X::BicondRandVar, A::BoolVar, B::BoolVar)
  C = nextvar!(bc)
  # auxilary variable C = A & B
  # (!A ∨ !B ∨ C) ∧ (A ∨ !C) ∧ (B ∨ !C)
#       //
#     // ( a_0 <-> a_1 )
#     //
#     // <=>
#     //
#     // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
#     //     (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
#     //

  bicond_subcnf = CMCNF([CMClause([CMLit(C,true),CMLit(A,false),CMLit(B,true)]),
                         CMClause([CMLit(C,true),CMLit(A,true), CMLit(B,false)]),
                         CMClause([CMLit(C,false),CMLit(A,false), CMLit(A,false)]),
                         CMClause([CMLit(C,false),CMLit(B,true), CMLit(C,true)])])
  push!(cnf, bicond_subcnf)
  C
end

# Not
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol, varset::VarSet, visited, bc::BoolCounter, X::NotRandVar, A::BoolVar)
  C = nextvar!(bc)
  # auxilary variable C = !A
  # (!A ∨ !C) ∧ (A ∨ C)
  not_subcnf = CMCNF([CMClause([CMLit(A,true),CMLit(C,true)]),
                      CMClause([CMLit(A,false),CMLit(C,false)])])
  push!(cnf, not_subcnf)
  C
end

# IfElse
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol, varset::VarSet, visited, bc::BoolCounter, X::IfElseRandVar, A::BoolVar, B::BoolVar, C::BoolVar)
  AUX = nextvar!(bc)
  # // aux = ( -aux | -a_0 |  a_1 ) &
  # //       ( -aux |  a_0 |  a_2 ) &
  # //       (  aux | -a_0 | -a_1 ) &
  # //       (  aux |  a_0 | -a_2 )
  # //
  aux_subcnf = CMCNF([CMClause([CMLit(AUX,true),CMLit(A,true),CMLit(B,false)]),
                      CMClause([CMLit(AUX,true),CMLit(A,false),CMLit(C,false)]),
                      CMClause([CMLit(AUX,false),CMLit(A,true),CMLit(B,true)]),
                      CMClause([CMLit(AUX,false),CMLit(C,true)])])
  push!(cnf, aux_subcnf)
  AUX
end

# Inequalities
for (name,op) in real_real_bool
  eval(
  quote
  function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                  varset::VarSet, visited, bc::BoolCounter, X::$name,
                  a::IBEX.ExprNode, b::IBEX.ExprNode)
    constraint::IBEX.ExprCtr = $op(a,b)
    boolvar = add_constraint!(cmap, constraint, varset, bc)
    boolvar
  end
  end)
end

# Real * Real -> Real
for (name,op) in real_real_real
  eval(
  quote
  # Real
  function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                  varset::VarSet, visited, bc::BoolCounter, X::$name,
                  a::IBEX.ExprNode, b::IBEX.ExprNode)
    result = ($op)(a,b)
    result
  end
  end)
end

# Real -> Real
for (name,op) in real_real
  eval(
  quote
  # Real
  function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                  varset::VarSet, visited, bc::BoolCounter, X::$name,
                  a::IBEX.ExprNode)
    result = ($op)(a)
    result
  end
  end)
end

# Real -> Floating
for (name,op) in real_floating
  eval(
  quote
  # Real
  function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                  varset::VarSet, visited, bc::BoolCounter, X::$name,
                  a::IBEX.ExprNode)
    result = ($op)(a)
    result
  end
  end)
end

# ifelse (real valued then and elsecase_constraint)
function expand(cmap::ConstraintMap, cnf::CMCNF, ω::IBEX.ExprSymbol,
                varset::VarSet, visited, bc::BoolCounter, X::IfElseRandVar,
                A::BoolVar, B::IBEX.ExprNode, C::IBEX.ExprNode)
  real_aux = IBEX.ExprSymbol()
  push!(varset, real_aux)
  thencase_constraint::IBEX.ExprCtr = real_aux == B
  elsecase_constraint::IBEX.ExprCtr = real_aux == C

  # Err, I think this is correct
  B_bool = add_constraint!(cmap, thencase_constraint, varset, bc)
  C_bool = add_constraint!(cmap, elsecase_constraint, varset, bc)
  bool_aux = expand(cmap, cnf, ω, varset, visited, bc, X, A, B_bool, C_bool)
  push!(cnf,CMClause([CMLit(bool_aux,false)])) # Assert that ifelse aux is true
  real_aux
end

# Maps Literal to Equation
type LiteralMap
  cxx
end

# Reverse direction and adds negation
function to_cxx_lmap(cmap::ConstraintMap)
  lmap = icxx"std::map<CMSat::Lit,ibex::ExprCtr>();"
  reverse_map = Dict(zip(values(cmap),keys(cmap)))

  for ((constraint, varset), boolvar) in cmap
    @show constraint
    @show varset

    # Don't make negative literal for equality constraints (from ifelses)
    if !icxx"$(constraint.cxx).op == ibex::EQ;"
      println("Found an equality constraint")
      negconstraint = !constraint
      negpair = icxx"std::pair<CMSat::Lit, ibex::ExprCtr>(CMSat::Lit($boolvar,true), $(negconstraint.cxx));"
      @cxx lmap->insert(negpair)
    end
    pair = icxx"std::pair<CMSat::Lit, ibex::ExprCtr>(CMSat::Lit($boolvar,false), $(constraint.cxx));"
    @cxx lmap->insert(pair)
  end
  LiteralMap(lmap)
end
