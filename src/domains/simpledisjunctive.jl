immutable SimpleDisjunctive{T} <: Domain{T}
  values::Set{T}
end

issubset(x::SimpleDisjunctive, y::SimpleDisjunctive) = issubset(x.values, y.values)
overlap(x::SimpleDisjunctive, y::SimpleDisjunctive) = intersect(x.values, y.values)
domaineq(x::SimpleDisjunctive, y::SimpleDisjunctive) = x.values == y.values
⊔{T}(x::SimpleDisjunctive{T},y::T) = push!(x.values, y)

function setmap{T}(f::Function, s::Set{T})
  out = Set{T}()
  for x in s
    push!(out,f(x))
  end
  out
end

# Real Valued Functiosn
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
for op = (:>, :>=, :<, :<=, :&, :|)
  @eval begin
    function ($op){T}(x::SimpleDisjunctive{T}, y::SimpleDisjunctive{T})
      let op = $op
        fcartproduct($op,Bool,x,y)
      end
    end
  end
end

# Boolean Valued Functions
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
  @show result
  for args in Iterators.product(x.values,y.values)
    ⊔(result, f(args...))
  end
  result
end
