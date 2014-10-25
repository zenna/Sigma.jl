type RandVarSymbolic{T} <: RandVar{T}
  ast::Expr
  compiled::Bool
  λ::Function

  # Precompiled
  RandVarSymbolic(ast::Expr, λ::Function) = new(ast,true,λ)
  RandVarSymbolic(ast::Expr) = new(ast,false)
end

## Constructors
RandVarSymbolic(T::DataType, e::Expr) = RandVarSymbolic{T}(e)

function compile!(X::RandVarSymbolic)
  if !X.compiled X.λ = eval(headexpr(X)) end
  X.compiled = true
  X
end
call!(X::RandVarSymbolic, ω) = (compile!(X); X.λ(ω))
callnocheck(X::RandVarSymbolic, ω) = X.λ(ω)
call!(f::Function, a) = f(a)

domaintype(X::RandVarSymbolic) = typeof(X).parameters[1]

## Conversion
## ============

# A constant random variable is a surjection which maps everything to constant c
# convert{T,E}(::Type{RandVarSymbolic{E}}, c::T) = RandVarSymbolic(T,:(ω -> $c))
convert{T}(::Type{RandVarSymbolic{T}}, c::T) = RandVarSymbolic(T,:($c))
promote_rule{T}(::Type{T}, ::Type{RandVarSymbolic{T}}) = RandVarSymbolic{T}
convert{E}(::Type{Function}, X::RandVarSymbolic{E}) = (compile!(X); X.λ)

## Abstractions
ast(X::RandVarSymbolic) = X.ast
# headexpr(X::RandVarSymbolic) = X.ast
# funcexpr(e::Expr) = e.args[2].args[2]
# headfuncexpr(X::RandVarSymbolic) = funcexpr(headexpr(X))

# Binary functions
for op = (:+, :-, :*, :/,:eq, :neq)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, Y::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(T, newast)
      end
    end

    ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
    ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:>, :>=, :<=, :<, :eq, :neq)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, Y::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, ast)
      end
    end

    ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
    ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:&, :|, :eq, :neq)
  @eval begin
    function ($op)(X::RandVarSymbolic{Bool}, Y::RandVarSymbolic{Bool})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, ast)
      end
    end

    ($op)(X::RandVarSymbolic, c::Bool) = ($op)(promote(X,c)...)
    ($op)(c::Bool, X::RandVarSymbolic) = ($op)(promote(c,X)...)
  end
end

# Lift unary primitve functions
for op = (:!,)
  @eval begin
    function ($op)(X::RandVarSymbolic{Bool})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(Bool, ast)
      end
    end
  end
end

# Lift unary primitve functions
for op = (:sqrt,:sqr,:abs,:round)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(T, ast)
      end
    end
  end
end
