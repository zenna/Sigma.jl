## =============
## Random Arrays
typealias RandomArray RandomVariable

for op = (:sum, :length)
  @eval begin
    function ($op)(a::RandomArray)
      ω->($op)(a(ω))
    end
  end
end

for op = (:dot,)
  @eval begin
    function ($op)(a::RandomArray, b::RandomArray)
      ω->($op)(a(ω),b(ω))
    end
  end
end

# Overloads rv[1,2]
getindex(rv::RandomArray, i::Integer, j::Integer) = ω->pipeomega(rv(ω)[i,j],ω)

## Functionally set a value in a random array
## This is inefficient
function setindex{T}(rv::RandomArray,v::T,i::Integer,j::Integer)
  ω->(a = rv(ω); [if (i == n) && (j == p) pipeomega(v,ω) else rv_push(a[n,p],ω) end
                  for n=1:size(a,1), p=1:size(a,2)])
end

## Creates a random array, which is a random variable, i.e. a function
## Given some ω as input it will return the array
## If the array contains random variables, ω will "pass" thrugh these aswell
function MakeRandomArray(t::DataType,x::Integer, y::Integer)
  a = Array(t,x,y)
  MakeRandomArray(a)
end

function MakeRandomArray(a::Array)
  ω->[rv_push(a[i,j],ω) for i=1:size(a,1), j=1:size(a,2)]
end

# Expets a unary primtive constructor
function independentRandomArray(constructor::Function, x::Integer, y::Integer, offset::Integer = 0)
  a = [constructor(i+(j-1)*(y-1)) for i = 1:x, j = 1:y]
  MakeRandomArray(a)
end

# The problem with smallest is that it requries we iterate over the list
uniformArray(l,u,x,y) = independentRandomArray(x->uniform(x,l,u),x,y)

function smallest(rv::RandomVariable, ra::RandomArray)
  function(ω)
    A = ra(ω)
    v = rv(ω)
    smallest = true
    for a in 1:length(A)
      smallest = smallest & v < A[i]
    end
    smallest
  end
end

dot(a,b) = a[1]*b[1] + a[2]*b[2]
