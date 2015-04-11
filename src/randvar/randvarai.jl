## Random Variables with Abstract Interpretation representation
## ============================================================

typealias LetExpr (Symbol, Any)

@doc "A Random Variable representation for use with abstract interpretation (AI)." ->
type RandVarAI{T} <: RandVar{T}
  ast
  lets::Vector{LetExpr}
  dims::Set{Int}
  compiled::Bool
  λ::Function
  RandVarAI(ast, lets, dims::Set{Int}, compiled::Bool) =
    new(ast,lets,dims,compiled)
end

@doc "Number of dimensions of sample space that X transforms" ->
ndims(X::RandVarAI) = length(X.dims)
ast(X::RandVarAI) = X.ast

@doc "construct an eval-able Lambda Expr from a RandVar" ->
function lambarise(X::RandVarAI)
  letexprs = [Expr(:(=),name,expr) for (name,expr) in X.lets]
  body = Expr(:let, X.ast, letexprs...)
  Expr(:->,:ω,body)
end

compile(X::RandVarAI) = eval(lambarise(X))

@doc "Compile RandVar into `Function`, store function in RandVar" ->
function compile!(X::RandVarAI)
  if !X.compiled X.λ = compile(X) end
  X.compiled = true
  X
end

function RandVarAI(T::DataType,ast,dims::Set{Int})
  name = genvar()
  RandVarAI{T}(name, [(name, ast)], dims, false)
end

function RandVarAI(T::DataType, ast,lets, dims::Set{Int})
  RandVarAI{T}(ast, lets, dims, false)
end

# Convenience
RandVarAI(T::DataType,ast,dim::Int) = RandVarAI(T,ast,Set(dim))

@doc "X(ω): A RandVar represents a function.  Call applies it to an argument" ->
call(X::RandVarAI, ω; args...) = (compile!(X); X.λ(ω))
callnocheck(X::RandVarAI, ω) = X.λ(ω)
rangetype(X::RandVarAI) = typeof(X).parameters[1]

## Lifted Functions of Random Variables
## ====================================

# Just concat lets without duplicates
function combinelets(randvars::RandVarAI...)
  seen = Set{LetExpr}()
  lets = LetExpr[]
  for rv in randvars
    for alet in rv.lets
      if !(alet in seen)
        push!(seen,alet)
        push!(lets,alet)
      end
    end
  end
  lets
end

# @doc """
#   Combine the lets for all the RandVars in the correct order.
#   e.g. A.lets: let x = rand(ω), y = sqrt(x)
#        B.lets: let y = sqrt(x), z = inc(y)

#   For some operation of A and B we need to combine them lets
#   in correct order so that dependencies are ok, e.g. the following would be bad
#   C = A + B
#   C.lets =  let y = sqrt(x), z = inc(y), x = rand(ω)
# """ ->
# function combinelets(randvars::RandVarAI...)
#   children = Dict{LetExpr,Vector{LetExpr}}()
#   nparents = Dict{LetExpr,Int}()

#   # Initialise empty dicts
#   for rv in randvars, alet in rv.lets
#     children[alet] = LetExpr[]
#     nparents[alet] = 0
#   end

#   # Create chain graph where each LetExpr is parent of next in list
#   # Nodes shared among randvars are parents of ALL nodes that follow them
#   for rv in randvars
#     for i = 1:length(rv.lets) - 1
#       push!(children[rv.lets[i]],rv.lets[i+1])
#       nparents[rv.lets[i+1]] += 1
#     end
#   end

#   # Running storage of nodes with no parents
#   noparents = LetExpr[]
#   for (alet, np) in nparents
#     np == 0 && push!(noparents, alet)
#   end
#   println("Before," ,length(noparents))

#   if length(noparents) == 0
#     for rv in randvars
#       println([alet[1] for alet in rv.lets])
#     end
#   end
#   lets = LetExpr[] #final sequence of lets
#   while length(lets) != length(nparents)
#     length(noparents) == 0 && error("noparents empty $(length(lets)) - $(length(nparents))")
#     currnode = pop!(noparents)
#     push!(lets, currnode)

#     # Break edge from that node to each of its children
#     for child in children[currnode]
#       np = nparents[child]
#       nparents[child] = np - 1
#       np - 1 == 0 && push!(noparents, child)
#     end
#   end
#   lets
# end

## RandVarSMT Algebra
## ==================
function combine(ast::Expr,RETURNT::DataType,randvars::RandVarAI...)
  name = genvar()
  combined_lets = combinelets(randvars...)
  # Append new ast as a let and make the ast just a symbol
  all_lets = vcat(combined_lets, (name, ast))
  combined_dims = union([X.dims for X in randvars]...)
  RandVarAI(RETURNT, name, all_lets, combined_dims)
end

@doc """
  Pointwise function lifting
  If `X` and `Y` are both random variables, `f(op,X,Y) = Z` where
  Z is a random variable defined as

  ```
  Z(ω) = X(ω) + Y(ω)
  ```
  """ ->
function lift(op,X::RandVarAI,Y::RandVarAI,RETURNT::DataType)
  newast = :(($op)($(ast(X)),$(ast(Y))))
  combine(newast,RETURNT,X,Y)
end

@doc "Lift op(X,c) where c is not RandVar" ->
function lift(op,X::RandVarAI,c,RETURNT::DataType)
  newast = :($op($(ast(X)),$c))
  combine(newast,RETURNT,X)
end

@doc "Lift op(c,X) where c is not RandVar" ->
function lift(op,c,X::RandVarAI,RETURNT::DataType)
  newast = :($op($c,$(ast(X))))
  combine(newast,RETURNT,X)
end

@doc "Unary Lift op(X)" ->
function lift(op,X::RandVarAI,RETURNT::DataType)
  newast = :($op($(ast(X))))
  combine(newast,RETURNT,X)
end

# TODO: Get rid of other lifts, perf diff is minimal to 0
@doc """
  Pointwise Lifting - arbitrary arity
  This generalises the other lift methods, but is a litle slower.
  """ ->
function lift_ai(op,RETURNT::DataType,args...)
  ast_args = Any[]
  randvar_args = RandVarAI[]
  for arg in args
    if isa(arg,RandVarAI)
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
for op = (:+, :-, :*)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarAI{T1}, Y::RandVarAI{T2}) = lift($op,X,Y,promote_type(T1, T2))
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarAI{T1}, c::T2) = lift($op,X,c,promote_type(T1, T2))
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarAI{T2}) = lift($op,c,X,promote_type(T1, T2))
end

# ## Real -> Real ##
abs{T}(X::RandVarAI{T}) = lift(abs,X,Y,T)

# ## Real × Real -> Bool ##
for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarAI{T1}, Y::RandVarAI{T2}) = lift($op,X,Y,Bool)
  @eval ($op){T1<:Real, T2<:Real}(X::RandVarAI{T1}, c::T2) = lift($op,X,c,Bool)
  @eval ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarAI{T2}) = lift($op,c,X,Bool)
end

# ## Real × Real -> Bool ##
for op = (:&, :|)
  @eval ($op)(X::RandVarAI{Bool}, Y::RandVarAI{Bool}) = lift($op,X,Y,Bool)
  @eval ($op)(X::RandVarAI{Bool}, c::Bool) = lift($op,X,c,Bool)
  @eval ($op)(c::Bool, X::RandVarAI{Bool}) = lift($op,c,X,Bool)
end

# ## Bool -> Bool ##
!(X::RandVarAI{Bool})= lift(!,X,Bool)

## ifelse
ifelse{T}(A::RandVarAI{Bool}, B::RandVarAI{T}, C::RandVarAI{T}) =
  lift_ai(ifelse,T,A,B,C)

ifelse{T1<:Real}(A::RandVarAI{Bool}, B::T1, C::T1) =
  lift_ai(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarAI{Bool}, B::RandVarAI{T1}, C::T1) =
  lift_ai(ifelse,T1,A,B,C)

ifelse{T1<:Real}(A::RandVarAI{Bool}, B::T1, C::RandVarAI{T1}) =
  lift_ai(ifelse,T1,A,B,C)

# ## Printing
# ## ========
# string(x::RandVarSMT{Bool}) = convert(SExpr, x, Omega()).e
# print(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
# show(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
# showcompact(io::IO, x::RandVarSMT{Bool}) = print(io, string(x))
