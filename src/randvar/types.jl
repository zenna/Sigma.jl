## Types and Arithmetic
## ====================
# Create types for each functional expression and overload primitive functions such
# randvar1 + randvar2 creates a PlusRandVar value with args [randvar1, randvar2]

## Constant Random Variable
## ========================
@doc "A constant value. A constant function which 'ignores' input, e.g. ω->5" ->
immutable ConstantRandVar{T} <: RandVar{T}
  val::T
end

args(X::ConstantRandVar) = Set{RandVar}()
dims(X::ConstantRandVar) = Set{Int}()
# QUESTION: Would this ever be called? Do we need to overload functiosn for all constants?
(==)(X::ConstantRandVar, Y::ConstantRandVar) = ConstantRandVar{Bool}(X.val == Y.val)
isequal(X::ConstantRandVar, Y::ConstantRandVar) = isequal(X.val,Y.val)

## Omega Random Variable
## =====================
@doc "Simplest RandVar: ω->ω[dim] - extracts dim component of omega" ->
immutable OmegaRandVar{T} <: RandVar{T}
  dim::Int
end

args(X::OmegaRandVar) = Set{RandVar}()
dims(X::OmegaRandVar) = Set(X.dim)
omega_component{T<:Real}(i,OmegaType::Type{T}=Float64) = OmegaRandVar{OmegaType}(i)
isequal(X::OmegaRandVar,Y::OmegaRandVar) = isequal(X.dim,Y.dim)

## Real × Real -> Real
## ===================
real_real_real = ((:PlusRandVar,:+),(:MinusRandVar,:-),(:TimesRandVar,:*),(:DivideRandVar,:/), (:PowRandVar,:(^)))
for (name,op) in real_real_real
  eval(
  quote
  immutable $name{T<:Real,A1<:Real,A2<:Real} <: RandVar{T}
    args::Tuple{RandVar{A1},RandVar{A2}}
  end
  # (^) Fixes ambiguities. Redefined here in each loop iteration but shouldn't matter
  (^){T1<:Real,T2<:Integer}(X::RandVar{T1},c::T2) = PowRandVar{promote_type(T1, T2),T1,T2}((X,c))
  ($op){T1<:Real, T2<:Real}(X::RandVar{T1}, Y::RandVar{T2}) = $name{promote_type(T1, T2),T1,T2}((X,Y))
  ($op){T1<:Real, T2<:Real}(X::RandVar{T1}, c::T2) = $name{promote_type(T1, T2),T1,T2}((X,ConstantRandVar(c)))
  ($op){T1<:Real, T2<:Real}(c::T1, X::RandVar{T2}) = $name{promote_type(T1, T2),T1,T2}((ConstantRandVar(c),X))
  end)
end

# Real -> Real
## ===========
for (name,op) in ((:UnaryPlusRandVar,:+),(:UnaryMinusRandVar,:-),(:AbsRandVar,:*))
  eval(
  quote
  immutable $name{T<:Real,A1<:Real} <: RandVar{T}
    args::Tuple{RandVar{A1}}
  end
  ($op){T<:Real}(X::RandVar{T}) = $name{T,T}((X,))
  end)
end

# Real -> _<:Floating
## ==================
for (name,op) in ((:ExpRandVar,:exp), (:LogRandVar,:log), (:SinRandVar,:sin),
          (:CosRandVar,:cos), (:TanRandVar,:tan), (:AsinRandVar,:asin),
          (:AcosRandVar,:acos), (:AtanRandVar,:atan), (:SinhRandVar,:sinh),
          (:CoshRandVar,:cosh), (:TanhRandVar,:tanh), (:Atan2RandVar,:atan2))
  eval(
  quote
  immutable $name{T<:Real,A1<:Real} <: RandVar{T}
    args::Tuple{RandVar{A1}}
  end
  ($op){T<:Real}(X::RandVar{T}, returntype::DataType = Float64) = $name{returntype,T}((X,))
  end)
end

# Real × Real -> Bool
## ===================
real_real_bool = ((:GTRandVar, :>), (:GTERandVar,:>=), (:LTERandVar,:<=), (:LTRandVar,:<),
                  (:EqRandVar, :(==)), (:NeqRandVar, :!=))

for (name,op) in real_real_bool
  eval(
  quote
  immutable $name{T<:Real,A1<:Real,A2<:Real} <: RandVar{T}
    args::Tuple{RandVar{A1},RandVar{A2}}
  end
  ($op){T1<:Real, T2<:Real}(X::RandVar{T1}, Y::RandVar{T2}) = $name{Bool,T1,T2}((X,Y))
  ($op){T1<:Real, T2<:Real}(X::RandVar{T1}, c::T2) = $name{Bool,T1,T2}((X,ConstantRandVar(c)))
  ($op){T1<:Real, T2<:Real}(c::T1, X::RandVar{T2}) = $name{Bool,T1,T2}((ConstantRandVar(c),X))
  end)
end

## Real × Real -> Bool
## ===================
for (name,op) in ((:OrRandVar, :|), (:AndRandVar,:&))
  eval(
  quote
  immutable $name{T,A1,A2} <: RandVar{Bool}
    args::Tuple{RandVar{A1},RandVar{A2}}
  end
  ($op)(X::RandVar{Bool}, Y::RandVar{Bool}) = $name{Bool,Bool,Bool}((X,Y))
  ($op)(X::RandVar{Bool}, c::Bool) = $name{Bool,Bool,Bool}((X,ConstantRandVar(c)))
  ($op)(c::Bool, X::RandVar{Bool}) = $name{Bool,Bool,Bool}((ConstantRandVar(c),X))
  end)
end

## Bool -> Bool
## ============
immutable NotRandVar{T,A1} <: RandVar{Bool}
  args::Tuple{RandVar{A1}}
end
!(X::RandVar{Bool})= NotRandVar{Bool,Bool}(X)

immutable IfElseRandVar{T,A1,A2,A3} <: RandVar{T}
  args::Tuple{RandVar{A1},RandVar{A2},RandVar{A3}}
end

## ifelse
## ======
ifelse{T}(A::RandVar{Bool}, B::RandVar{T}, C::RandVar{T}) = IfElseRandVar{T,Bool,T,T}((A,B,C))
ifelse{T<:Real}(A::RandVar{Bool}, B::T, C::T) = IfElseRandVar{T,Bool,T,T}((A,ConstantRandVar(B),ConstantRandVar(C)))
ifelse{T<:Real}(A::RandVar{Bool}, B::RandVar{T}, C::T) = IfElseRandVar{T,Bool,T,T}((A,B,ConstantRandVar(C)))
ifelse{T<:Real}(A::RandVar{Bool}, B::T, C::RandVar{T}) = IfElseRandVar{T,Bool,T,T}((A,ContantRandVar(B),C))

# Unions
## =====
BinaryRealExpr = Union(PlusRandVar, MinusRandVar, TimesRandVar,DivideRandVar,PowRandVar)
UnaryRealExpr = Union(UnaryPlusRandVar,UnaryMinusRandVar,AbsRandVar)
TrigExpr = Union(ExpRandVar,LogRandVar,SinRandVar,CosRandVar,TanRandVar,AsinRandVar,
                 AcosRandVar,AtanRandVar,SinhRandVar,CoshRandVar,TanhRandVar,Atan2RandVar)
IneqExpr = Union(GTRandVar,GTERandVar,LTERandVar, LTRandVar,EqRandVar,NeqRandVar)
LogicalExpr = Union(OrRandVar,AndRandVar)

# All Functional expressions
FuncionalExpr = Union(BinaryRealExpr, UnaryRealExpr, TrigExpr, IneqExpr, LogicalExpr, IfElseRandVar)

args{T<:FuncionalExpr}(X::T) = X.args