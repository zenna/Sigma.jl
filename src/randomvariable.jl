typealias RandomVariable Function

type RandomVariableSymbolic
  asts::Vector{Expr}
  compiled::Bool
  λ::Function

  # Precompiled
  RandomVariableSymbolic(asts::Vector{Expr}, λ::Function) = new(asts,true,λ)
  RandomVariableSymbolic(asts::Vector{Expr}) = new(asts,false)
end

# TODO
RandomVariableSymbolic(e::Expr) = RandomVariableSymbolic([e])
function compile!(X::RandomVariableSymbolic)
  if !X.compiled X.λ = eval(headexpr(X)) end
  X.compiled = true
  X
end
call!(X::RandomVariableSymbolic, ω) = (compile!(X); X.λ(ω))

## Conversion
## ============

# A constant random variable is a surjection which maps everything to constant c
convert(::Type{RandomVariableSymbolic}, c::ConcreteReal) = RandomVariableSymbolic(:(ω -> $c))
promote_rule{T<:ConcreteReal}(::Type{T}, ::Type{RandomVariableSymbolic}) = RandomVariableSymbolic
convert(::Type{Function}, X::RandomVariableSymbolic) = X.λ

headexpr(X::RandomVariableSymbolic) = X.asts[1]
# funcexpr(e::Expr) = e.args[2]
funcexpr(e::Expr) = e.args[2].args[2]
headfuncexpr(X::RandomVariableSymbolic) = funcexpr(headexpr(X))


omega(i::Int64) = RandomVariableSymbolic(:(X(ω) -> ω[$i]))

# Binary functions
for op = (:+, :-, :*, :/, :&, :|, :$, :>, :>=, :<=, :<, :eq, :neq)
  @eval begin
    function ($op)(X::RandomVariableSymbolic, Y::RandomVariableSymbolic)
      let op = $op
        newheadexpr = :(ω -> $op($(headfuncexpr(X)),$(headfuncexpr(Y))))
        RandomVariableSymbolic(newheadexpr)
      end
    end

    ($op)(X::RandomVariableSymbolic, c::ConcreteReal) = ($op)(promote(X,c)...)
    ($op)(c::ConcreteReal, X::RandomVariableSymbolic) = ($op)(promote(c,X)...)
  end
end

# Lift primitive operators to work on random variables
# A function applied to a random variable evaluates to
# a random variable

# Binary functions
for op = (:+, :-, :*, :/, :&, :|, :$, :>, :>=, :<=, :<, :eq, :neq)
  @eval begin
    function ($op)(a::RandomVariable, b::RandomVariable)
      f(ω) = ($op)(a(ω),b(ω))
    end
    function ($op)(a::Number, b::RandomVariable)
      f(ω) = ($op)(a,b(ω))
    end
    function ($op)(a::RandomVariable, b::Number)
      f(ω) = ($op)(a(ω),b)
    end
  end
end

# Lift unary functions
for op = (:!,:sqrt,:sqr,:abs,:round)
  @eval begin
    function ($op)(a::RandomVariable)
      f(ω) = ($op)(a(ω))
    end
  end
end
