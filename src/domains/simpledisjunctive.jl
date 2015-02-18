## Disjuncive Domain A1 ∨ A2 ∨ A3 ∨ ... ∨ An
## =================================================================

# This is a simple non-relational domain of disjunctive domains (paramaterised by T)

immutable SimpleDisjunctive{T} <: Domain{T}
  values::Set{T}
end

isrelational(::Union(SimpleDisjunctive, Type{SimpleDisjunctive})) = false

## Set Operations
## ==============
issubset(x::SimpleDisjunctive, y::SimpleDisjunctive) = issubset(x.values, y.values)
overlap(x::SimpleDisjunctive, y::SimpleDisjunctive) = intersect(x.values, y.values)
domaineq(x::SimpleDisjunctive, y::SimpleDisjunctive) = x.values == y.values
⊔{T}(x::SimpleDisjunctive{T},y::T) = push!(x.values, y)

# Apply f to every abstract element in disjunction
function setmap{T}(f::Function, s::Set{T})
  out = Set{T}()
  for x in s
    push!(out,f(x))
  end
  out
end

# Operations on Disjunctive Domains (to be sound) do a cartesian product
# Real × Real ->  Rea
for op = (:+, :-, :*, :/)
  @eval begin
    function ($op){T}(x::SimpleDisjunctive{T}, y::SimpleDisjunctive{T})
      let op = $op
        fcartproduct($op,T,x,y)
      end
    end
  end
end

# Boolean Valued Functions
# Real × Real ->  Rea
for op = (:>, :>=, :<, :<=, :&, :|)
  @eval begin
    function ($op){T}(x::SimpleDisjunctive{T}, y::SimpleDisjunctive{T})
      let op = $op
        fcartproduct($op,Bool,x,y)
      end
    end
  end
end

# Real ->  Rea
for op = (:sqr,)
  @eval begin
    function ($op){T}(x::SimpleDisjunctive{T})
      let op = $op
        SimpleDisjunctive{T}(setmap(op,x.values))
      end
    end
  end
end

function !(x::SimpleDisjunctive{Bool})
  if x.values == Set{Bool}(true) SimpleDisjunctive{Bool}(Set(false))
  elseif x.values == Set{Bool}(false) SimpleDisjunctive{Bool}(Set(true))
  else x end
end

# Apply f to the cartesian product of values in x and y
function fcartproduct(f::Function, T::DataType,
                      x::SimpleDisjunctive, y::SimpleDisjunctive)
  result = SimpleDisjunctive{T}(Set{T}())
  for args in Iterators.product(x.values,y.values)
    ⊔(result, f(args...))
  end
  result
end
