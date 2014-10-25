typealias RandVar{T} RandomVariable{T}

# Rundown of approach
# ===================
# - A RandomVariable may have multiple representations
# - There exist equivalences between them.
# - We assume for any given relation are at most two equivalences
# - e.g random(1) * random(2) = (ω -> ω[1]) * (ω -> ω[2]) = ω -> ω[1] * ω[2]
# - In this case that the terms are the left,center and right.
# - A random variable will always have a center, but may not have a left or right (when there are no more)
#   reductions
# - RandomVariable store

# RandVar which accesses ith component of ω
immutable PrimitiveRandVar{T} <: RandVar{T}
  i::Integer
end

left(X::PrimitiveRandVar) = X
center(X::PrimitiveRandVar) = :(random($(X.i)))
right{T}(X::PrimitiveRandVar{T}) = λRandVar{T}(X, :(ω -> ω[$(X.i)]))

# RandVar in symbolic functionalm for - :(ω -> ...)
immutable λRandVar{T} <: RandVar{T}
  left::RandomVariable
  code::Expr
end

left(X::λRandVar) = X.left
center(X::λRandVar) = X.code
right(X::λRandVar) = X # No more reductions

body(e::λRandVar) = e.code.args[2].args[2]

type ComplexRandVar{T} <: RandVar{T}
  code::Expr
  left::RandomVariable

  ComplexRandVar(code::Expr,old::RandomVariable) = new(code,old)

  function ComplexRandVar(code::Expr)
    X = new(code)
    X.left = X
    X
  end
end

left(X::ComplexRandVar) = X.left
center(X::ComplexRandVar) = X.code
function right{T}(X::ComplexRandVar{T})
  newcenter = postwalk(s-> if isa(s,RandVar) right(s) else s end, X.code)
  ComplexRandVar{T}(newcenter,X)
end

# Results from function which constructs new random variables
# e.g. uniform(0,1) where we might want to keep bothform around
# but we need to go inside the funciton to expand
immutable ConstructorRandVar{T} <: RandVar{T}
  e1::Expr
  e2::Expr
end

## Walk
## ====

postwalkjump(f::Function, a) = f(a)
postwalkjump(f::Function, e::Expr) = postwalk(f,e)

function postwalk(f::Function, e::Expr)
  newargs = eltype(e.args)[]
  exprcopy = deepcopy(e) #Or just copy?
   for a in exprcopy.args
    push!(newargs, postwalkjump(f,a))
  end
  exprcopy.args = newargs
  exprcopy
end

## Primitive Functions
## ===================

randomy(i) = PrimitiveRandVar{Float64}(i)

## RandomVariable Arithmetic
## =========================

*(A::PrimitiveRandVar{Float64}, B::Integer) = ComplexRandVar{Float64}(:($A * $B))
*(A::λRandVar, B::λRandVar) = λRandVar(:(ω -> (*)($(body(X)),$(body(Y)))))
*(A::λRandVar, B::Real) = λRandVar(:(ω -> (*)($(body(X)),$B)))
myF(X) = X > uniform(0,1)
myF(X::ComplexRandVar) = ConstructorRandVar(:(myF($X)), myF(X))

## Example
## =======

# right(B)

# C = sqr(B)
# D = myf(C)


# A = random(1)
# left(A) = :(random(1))
# right(A) = :(ω -> ω[1])

# B = A * 5
# left(B) = :(A * 5)
# right(B) = :((ω -> ω[1]) * 5)
# right(right(B)) = :(ω -> ω[1] * 5)

# C = sqr(B)
# left(C) = :(sqr(B))
# right(C) = :(sqr(ω -> ω[1] * 5))
# right(right(C)) = :(ω -> sqr(ω[1] * 5))

# D = myf(C)
# left(D) = :(myF(C))
# right(D) = :(X::RV > Y::RV)
# right(right(D)) = :(ω -> )

# left(B) = :(random(1) * 5)
# right(B) = :(ω -> ω[1] * 5)
