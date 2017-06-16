## SymbolicRandVar
## ===============
"Return a Set of dimension indices of a random variable"
function dims(X::SymbolicRandVar)
  # Do a depth first search and find union of dimensions of all OmegaRandVars
  dimensions = Set{Int}()
  visited = Set{RandVar}()
  tovisit = Set{RandVar}([X])
  while !isempty(tovisit)
    v = pop!(tovisit)
    if has_single_dim(v)
      push!(dimensions, v.dim)
    end
    for arg in args(v)
      arg ∉ visited && push!(tovisit,arg)
    end
  end
  dimensions
end

# "Apply a random variable to some randomness"
# call(X::SymbolicRandVar,ω) = lambda(X)(ω)

# Base case is that symbolic rand vars have multiple dims
has_single_dim(X::SymbolicRandVar) = false

function isequal(X::SymbolicRandVar, Y::SymbolicRandVar)
  # Equivalent Random variables should (at least) have same type and #args
  typeof(X) != typeof(Y) && (return false)
  x_args = fields(X)
  y_args = fields(Y)
  length(x_args) != length(y_args) && (return false)
  for i = 1:length(x_args)
    !isequal(x_args[i],y_args[i]) && (return false)
  end
  true
end

in{T}(X::SymbolicRandVar, bounds::Tuple{Lift{T},Lift{T}}) = (X >= bounds[1]) & (X <=  bounds[2])

## Constant Random Variable
## ========================
"A constant value. A constant function which 'ignores' input, e.g. ω->5"
immutable ConstantRandVar{T} <: SymbolicRandVar{T}
  val::T
end

args(X::ConstantRandVar) = tuple()
dims(X::ConstantRandVar) = Set{Int}()
# QUESTION: Would this ever be called? Do we need to overload functiosn for all constants?
(==)(X::ConstantRandVar, Y::ConstantRandVar) = ConstantRandVar{Bool}(X.val == Y.val)
isequal(X::ConstantRandVar, Y::ConstantRandVar) = isequal(X.val,Y.val)

# FIXME: Hack? Maybe the need for this will go away if RandArrays are of SymbolicRandVar
one{T}(::Type{RandVar{T}}) = ConstantRandVar(one(T))
zero{T}(::Type{RandVar{T}}) = ConstantRandVar(zero(T))
zero{T}(::RandVar{T}) = ConstantRandVar(zero(T))
norm(X::ConstantRandVar) = ConstantRandVar(norm(X.val))

one{T}(::Type{SymbolicRandVar{T}}) = ConstantRandVar(one(T))
zero{T}(::Type{SymbolicRandVar{T}}) = ConstantRandVar(zero(T))

real{T}(X::SymbolicRandVar{T}) = X

## Omega Random Variable
## =====================
"Simplest RandVar: ω->ω[dim] - extracts dim component of omega"
immutable OmegaRandVar{T} <: SymbolicRandVar{T}
  dim::Int
end

args(X::OmegaRandVar) = Set{RandVar}()
dims(X::OmegaRandVar) = Set(X.dim)
omega_component{T<:Real}(i,OmegaType::Type{T}=Float64) = OmegaRandVar{OmegaType}(i)
omega_component{T<:Real}(OmegaType::Type{T}=Float64) = OmegaRandVar{OmegaType}(genint())
isequal(X::OmegaRandVar,Y::OmegaRandVar) = isequal(X.dim,Y.dim)
has_single_dim(X::OmegaRandVar) = true

## Real × Real -> Real
## ===================
real_real_real = ((:PlusRandVar,:+),(:MinusRandVar,:-),(:TimesRandVar,:*),(:DivideRandVar,:/), (:PowRandVar,:(^)))
for (name,op) in real_real_real
  eval(
  quote
  immutable $name{T<:Real,A1<:Real,A2<:Real} <: SymbolicRandVar{T}
    args::Tuple{SymbolicRandVar{A1},SymbolicRandVar{A2}}
  end
  # (^) Fixes ambiguities. Redefined here in each loop iteration but shouldn't matter
  # (^){T1<:Real,T2<:Integer}(X::SymbolicRandVar{T1},c::T2) = PowRandVar{promote_type(T1, T2),T1,T2}((X,ConstantRandVar(c)))
  ($op){T1<:Real, T2<:Real}(X::SymbolicRandVar{T1}, Y::SymbolicRandVar{T2}) = $name{promote_type(T1, T2),T1,T2}((X,Y))
  ($op){T1<:Real, T2<:Real}(X::SymbolicRandVar{T1}, c::T2) = $name{promote_type(T1, T2),T1,T2}((X,ConstantRandVar(c)))
  ($op){T1<:Real, T2<:Real}(c::T1, X::SymbolicRandVar{T2}) = $name{promote_type(T1, T2),T1,T2}((ConstantRandVar(c),X))
  end)
end

# Real -> Real
## ===========
real_real = ((:UnaryPlusRandVar,:+),(:UnaryMinusRandVar,:-),(:AbsRandVar,:abs))
for (name,op) in real_real
  eval(
  quote
  immutable $name{T<:Real, A1<:Real} <: SymbolicRandVar{T}
    args::Tuple{SymbolicRandVar{A1}}
  end
  ($op){T<:Real}(X::SymbolicRandVar{T}) = $name{T,T}((X,))
  end)
end

# Real -> _<:Floating
## ==================
real_floating = (
  (:SqrtRandVar, :sqrt), (:ExpRandVar,:exp), (:LogRandVar,:log), (:SinRandVar,:sin),
  (:CosRandVar,:cos), (:TanRandVar,:tan), (:AsinRandVar,:asin),
  (:AcosRandVar,:acos), (:AtanRandVar,:atan), (:SinhRandVar,:sinh),
  (:CoshRandVar,:cosh), (:TanhRandVar,:tanh), (:Atan2RandVar,:atan2))

for (name,op) in real_floating
  eval(
  quote
  immutable $name{T<:Real,A1<:Real} <: SymbolicRandVar{T}
    args::Tuple{SymbolicRandVar{A1}}
  end
  ($op){T<:Real}(X::SymbolicRandVar{T}, returntype::DataType = Float64) = $name{returntype,T}((X,))
  end)
end

# Real × Real -> Bool
## ===================
real_real_bool = ((:GTRandVar, :>), (:GTERandVar,:>=), (:LTERandVar,:<=), (:LTRandVar,:<),
                  (:EqRandVar, :(==)), (:NeqRandVar, :!=))

for (name,op) in real_real_bool
  eval(
  quote
  immutable $name{T<:Real,A1<:Real,A2<:Real} <: SymbolicRandVar{T}
    args::Tuple{SymbolicRandVar{A1},SymbolicRandVar{A2}}
  end
  ($op){T1<:Real, T2<:Real}(X::SymbolicRandVar{T1}, Y::SymbolicRandVar{T2}) = $name{Bool,T1,T2}((X,Y))
  ($op){T1<:Real, T2<:Real}(X::SymbolicRandVar{T1}, c::T2) = $name{Bool,T1,T2}((X,ConstantRandVar(c)))
  ($op){T1<:Real, T2<:Real}(c::T1, X::SymbolicRandVar{T2}) = $name{Bool,T1,T2}((ConstantRandVar(c),X))
  end)
end

## Real × Real -> Bool
## ===================
bool_bool_bool = ((:OrRandVar, :|), (:AndRandVar,:&), (:BicondRandVar, :(==)))
for (name,op) in bool_bool_bool
  eval(
  quote
  immutable $name{T,A1,A2} <: SymbolicRandVar{Bool}
    args::Tuple{SymbolicRandVar{A1},SymbolicRandVar{A2}}
  end
  ($op)(X::SymbolicRandVar{Bool}, Y::SymbolicRandVar{Bool}) = $name{Bool,Bool,Bool}((X,Y))
  ($op)(X::SymbolicRandVar{Bool}, c::Bool) = $name{Bool,Bool,Bool}((X,ConstantRandVar(c)))
  ($op)(c::Bool, X::SymbolicRandVar{Bool}) = $name{Bool,Bool,Bool}((ConstantRandVar(c),X))
  end)
end

## Bool -> Bool
## ============
immutable NotRandVar{T,A1} <: SymbolicRandVar{Bool}
  args::Tuple{SymbolicRandVar{A1}}
end
!(X::SymbolicRandVar{Bool})= NotRandVar{Bool,Bool}((X,))

immutable IfElseRandVar{T,A1,A2,A3} <: SymbolicRandVar{T}
  args::Tuple{SymbolicRandVar{A1},SymbolicRandVar{A2},SymbolicRandVar{A3}}
end

## ifelse
## ======
ifelse{T}(A::SymbolicRandVar{Bool}, B::SymbolicRandVar{T}, C::SymbolicRandVar{T}) = IfElseRandVar{T,Bool,T,T}((A,B,C))
ifelse{T<:Real}(A::SymbolicRandVar{Bool}, B::T, C::T) = IfElseRandVar{T,Bool,T,T}((A,ConstantRandVar(B),ConstantRandVar(C)))
ifelse{T<:Real}(A::SymbolicRandVar{Bool}, B::SymbolicRandVar{T}, C::T) = IfElseRandVar{T,Bool,T,T}((A,B,ConstantRandVar(C)))
ifelse{T<:Real}(A::SymbolicRandVar{Bool}, B::T, C::SymbolicRandVar{T}) = IfElseRandVar{T,Bool,T,T}((A,ConstantRandVar(B),C))

# Unions
## =====
BinaryRealExpr = Union{PlusRandVar, MinusRandVar, TimesRandVar,DivideRandVar,PowRandVar}
UnaryRealExpr = Union{UnaryPlusRandVar,UnaryMinusRandVar,AbsRandVar}
TrigExpr = Union{ExpRandVar,LogRandVar,SinRandVar,CosRandVar,TanRandVar,AsinRandVar,
                 AcosRandVar,AtanRandVar,SinhRandVar,CoshRandVar,TanhRandVar,Atan2RandVar}
IneqExpr = Union{GTRandVar,GTERandVar,LTERandVar, LTRandVar,EqRandVar,NeqRandVar}
LogicalExpr = Union{OrRandVar,AndRandVar, BicondRandVar, NotRandVar}

# All Functional expressions
CompositeRandVar = Union{BinaryRealExpr, UnaryRealExpr, TrigExpr, IneqExpr, LogicalExpr, SqrtRandVar, IfElseRandVar}

args{T<:CompositeRandVar}(X::T) = X.args

## Printing
## ========
function to_dimacs(Y::SymbolicRandVar{Bool})
  cmap, cnf, ω, aux_vars = analyze(Y)
  indep_vars = join(values(cmap), " ")
  last_var = var(cnf[length(cnf)][1])
  println("cnf $last_var $(length(cnf))")
  println(string(cnf))
  println("c ind $indep_vars")
end
