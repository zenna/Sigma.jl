using FastAnonymous

type RandVarSymbolic{T} <: RandVar{T}
  ast
  compiled::Bool
  λ

  # Precompiled
  RandVarSymbolic(ast, λ::Function) = new(ast,true,λ)
  RandVarSymbolic(ast) = new(ast,false)
end

## Constructors
RandVarSymbolic(T::DataType, e) = RandVarSymbolic{T}(e)

lambarise(X::RandVarSymbolic) = :(ω->$(ast(X)))

function compile!(X::RandVarSymbolic)
  if !X.compiled X.λ = eval(:(@anon $(lambarise(X)))) end
  X.compiled = true
  X
end

# Call is state changing, but I've omitted ! so that that we can
# overload the () syntax.
call(X::RandVarSymbolic, ω) = (compile!(X); X.λ(ω))
callnocheck(X::RandVarSymbolic, ω) = X.λ(ω)

# Will need to deprecate this in v4.
call(f::Function, a) = f(a)

rangetype(X::RandVarSymbolic) = typeof(X).parameters[1]

## Conversion
## ============

# A constant random variable is a surjection which maps everything to constant c
# convert{T,E}(::Type{RandVarSymbolic{E}}, c::T) = RandVarSymbolic(T,:(ω -> $c))
convert{T}(::Type{RandVarSymbolic{T}}, c::T) = RandVarSymbolic(T,:($c))
promote_rule{T}(::Type{T}, ::Type{RandVarSymbolic{T}}) = RandVarSymbolic{T}
convert{E}(::Type{Function}, X::RandVarSymbolic{E}) = (compile!(X); X.λ)

## Abstractions
ast(X::RandVarSymbolic) = X.ast

# Binary functions
for op = (:+, :-, :*, :/, :(==), :!=)
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

for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, Y::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, newast)
      end
    end

    ($op){T<:ConcreteReal}(X::RandVarSymbolic{T}, c::T) = ($op)(promote(X,c)...)
    ($op){T<:ConcreteReal}(c::T, X::RandVarSymbolic{T}) = ($op)(promote(c,X)...)
  end
end

for op = (:&, :|, :(==), :!=)
  @eval begin
    function ($op)(X::RandVarSymbolic{Bool}, Y::RandVarSymbolic{Bool})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, newast)
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
        RandVarSymbolic(Bool, newast)
      end
    end
  end
end

# Lift unary primitve functions
for op = (:sqrt,:sqr,:abs)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(T, newast)
      end
    end
  end
end

# Lift unary primitve functions
for op = (:round,)
  @eval begin
    function ($op){T<:ConcreteReal}(X::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(Int64, newast)
      end
    end
  end
end


macro noexpand(dtype, fcall)
  @assert fcall.head == :call
  fname = fcall.args[1]
  fargs = fcall.args[2:end]
  quote
    pargs = vcat($(fargs...))
    callexpr = Expr(:call, $fname, pargs...)
    pipeexpr = Expr(:call, :pipeomega, callexpr, :ω)
    RandVarSymbolic($dtype, pipeexpr)
  end
end
