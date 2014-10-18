type RandomVariableSymbolic{E} <: RandomVariable
  asts::Vector{Expr}
  compiled::Bool
  λ::Function

  # Precompiled
  RandomVariableSymbolic(asts::Vector{Expr}, λ::Function) = new(asts,true,λ)
  RandomVariableSymbolic(asts::Vector{Expr}) = new(asts,false)
end

RandomVariableSymbolic(T::DataType, e::Expr) = RandomVariableSymbolic{T}([e])

function compile!(X::RandomVariableSymbolic)
  if !X.compiled X.λ = eval(headexpr(X)) end
  X.compiled = true
  X
end
call!(X::RandomVariableSymbolic, ω) = (compile!(X); X.λ(ω))
callnocheck(X::RandomVariableSymbolic, ω) = X.λ(ω)
call!(f::Function, a) = f(a)

domaintype(X::RandomVariableSymbolic) = typeof(X).parameters[1]

## Conversion
## ============

# A constant random variable is a surjection which maps everything to constant c
# convert{T,E}(::Type{RandomVariableSymbolic{E}}, c::T) = RandomVariableSymbolic(T,:(ω -> $c))
convert{T}(::Type{RandomVariableSymbolic{T}}, c::T) = RandomVariableSymbolic(T,:(ω -> $c))
promote_rule{T}(::Type{T}, ::Type{RandomVariableSymbolic{T}}) = RandomVariableSymbolic{T}
convert{E}(::Type{Function}, X::RandomVariableSymbolic{E}) = X.λ

headexpr(X::RandomVariableSymbolic) = X.asts[1]
# funcexpr(e::Expr) = e.args[2]
funcexpr(e::Expr) = e.args[2].args[2]
headfuncexpr(X::RandomVariableSymbolic) = funcexpr(headexpr(X))

# Binary functions
for op = (:+, :-, :*, :/,:eq, :neq)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandomVariableSymbolic{T}, Y::RandomVariableSymbolic{T})
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X)),$(headfuncexpr(Y))))
        RandomVariableSymbolic(T, newheadexpr)
      end
    end

    ($op){T<:ConcreteReal}(X::RandomVariableSymbolic{T}, c::T) = ($op)(promote(X,c)...)
    ($op){T<:ConcreteReal}(c::T, X::RandomVariableSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:>, :>=, :<=, :<, :eq, :neq)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandomVariableSymbolic{T}, Y::RandomVariableSymbolic{T})
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X)),$(headfuncexpr(Y))))
        RandomVariableSymbolic(Bool,newheadexpr)
      end
    end

    ($op){T<:ConcreteReal}(X::RandomVariableSymbolic{T}, c::T) = ($op)(promote(X,c)...)
    ($op){T<:ConcreteReal}(c::T, X::RandomVariableSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:&, :|, :eq, :neq)
  @eval begin
    function ($op)(X::RandomVariableSymbolic{Bool}, Y::RandomVariableSymbolic{Bool})
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X)),$(headfuncexpr(Y))))
        RandomVariableSymbolic(Bool,newheadexpr)
      end
    end

    ($op)(X::RandomVariableSymbolic, c::Bool) = ($op)(promote(X,c)...)
    ($op)(c::Bool, X::RandomVariableSymbolic) = ($op)(promote(c,X)...)
  end
end

# Lift unary primitve functions
for op = (:!,)
  @eval begin
    function ($op)(X::RandomVariableSymbolic{Bool})
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X))))
        RandomVariableSymbolic(Bool,newheadexpr)
      end
    end
  end
end

# Lift unary primitve functions
for op = (:sqrt,:sqr,:abs,:round)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandomVariableSymbolic{T})
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X))))
        RandomVariableSymbolic(T, newheadexpr)
      end
    end
  end
end
