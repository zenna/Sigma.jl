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
call(X::RandVarSymbolic, ω; args...) = (compile!(X); X.λ(ω))
callnocheck(X::RandVarSymbolic, ω) = X.λ(ω)

# Will need to deprecate this in Julia v4.
call(f::Function, a) = f(a)

rangetype(X::RandVarSymbolic) = typeof(X).parameters[1]

## Conversion
## ============

# A constant can be converted into a constant random variable
# which is a surjection which maps everything to constant c
convert{T}(::Type{RandVarSymbolic{T}}, c::T) = RandVarSymbolic(T,:($c))
promote_rule{T1<:Real, T2<:Real}(::Type{T1}, ::Type{RandVarSymbolic{T2}}) =
  RandVarSymbolic{promote_type(T1,T2)}

promote_rule{T<:Real}(::Type{T}, ::Type{RandVarSymbolic{T}}) = RandVarSymbolic{T}
promote_rule{T}(::Type{T}, ::Type{RandVarSymbolic{T}}) = RandVarSymbolic{T}

# Special case for conversion between Number types to allow e.g. uniform(0.,1.) + 3
convert{T<:Real}(::Type{RandVarSymbolic{T}}, c::T) = RandVarSymbolic(T,:($c))
convert{T1<:Real, T2<:Real}(::Type{RandVarSymbolic{T1}}, c::T2) =
  (T = promote_type(T1,T2); RandVarSymbolic(T,:($(convert(T,c)))) )



# Convert a random variable to a julia function by compiling the lambda
convert{E}(::Type{Function}, X::RandVarSymbolic{E}) = (compile!(X); X.λ)

## Abstractions
ast(X::RandVarSymbolic) = X.ast

# Binary functions, with Real output
for op = (:+, :-, :*, :/)
  @eval begin
    function ($op){T1<:Real, T2<:Real}(X::RandVarSymbolic{T1}, Y::RandVarSymbolic{T2})
      let op = $op
        RETURNT = promote_type(T1, T2)
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(RETURNT, newast)
      end
    end

    ($op){T1<:Real, T2<:Real}(X::RandVarSymbolic{T1}, c::T2) = ($op)(promote(X,c)...)
    ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarSymbolic{T2}) = ($op)(promote(c,X)...)
  end
end

# Real × Real -> Bool
for op = (:>, :>=, :<=, :<, :(==), :!=, :isapprox)
  @eval begin
    function ($op){T1<:Real, T2<:Real}(X::RandVarSymbolic{T1}, Y::RandVarSymbolic{T2})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, newast)
      end
    end

    ($op){T1<:Real, T2<:Real}(X::RandVarSymbolic{T1}, c::T2) = ($op)(promote(X,c)...)
    ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarSymbolic{T2}) = ($op)(promote(c,X)...)
  end
end

# Bool × Bool -> Bool
for op = (:&, :|, :(==), :!=)
  @eval begin
    function ($op)(X::RandVarSymbolic{Bool}, Y::RandVarSymbolic{Bool})
      let op = $op
        newast = :($op($(ast(X)),$(ast(Y))))
        RandVarSymbolic(Bool, newast)
      end
    end

    ($op)(X::RandVarSymbolic{Bool}, c::Bool) = ($op)(promote(X,c)...)
    ($op)(c::Bool, X::RandVarSymbolic{Bool}) = ($op)(promote(c,X)...)
  end
end

# Bool -> Bool
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

# Real -> Real
for op = (:sqr,:abs)
  @eval begin
    function ($op){T<:Real}(X::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(T, newast)
      end
    end
  end
end

# Real -> Float64
for op = (:sqrt,)
  @eval begin
    function ($op){T<:Real}(X::RandVarSymbolic{T})
      let op = $op
        newast = :($op($(ast(X))))
        RandVarSymbolic(Float64, newast)
      end
    end
  end
end

# Real -> Int
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

function in(X::RandVarSymbolic{Float64}, i::Vector{Float64})
  @assert length(i) == 2
  @assert i[1] <= i[2]
  (X >= i[1]) & (X <= i[2])
end
