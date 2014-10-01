# Disjunctive Interval Domain
# REVIEW: Decide whether to keep this, or whether it is redundant

using Iterators
immutable IntervalDisj
  intervals::Array{Float64,2}
end

function IntervalDisj{T<:Real}(x::T,y::T)
  a = Array(Float64,2,1)
  a[1,1] = x
  a[2,1] = y
  x,y = if x >= y y,x else x,y end
  IntervalDisj(a)
end

# Eliminate redundancy with interval domain
IntervalDisj(x::Interval) = IntervalDisj(x.l,x.u)
IntervalDisj(x::Vector) = IntervalDisj(x[1],x[2])
IntervalDisj(x::Interval,y::Interval) = ⊔(IntervalDisj([x.l y.l
                                                        x.u y.u]))
getindex(x::IntervalDisj,i::Int64,j::Int64) = x.intervals[i,j]
numelems(x::IntervalDisj) = size(x.intervals,2)

nthinterval(x::IntervalDisj, i::Integer) = IntervalDisj(x[1,i],x[2,i])

function crossdisj(f::Function, x::IntervalDisj, y::IntervalDisj)
  if numelems(x) == numelems(y) == 1
    ⊔(f(x,y))
  else
    A = x.intervals
    B = y.intervals
    D = [A[:,i] for i = 1:size(A,2)]
    E = [B[:,i] for i = 1:size(B,2)]

    intervals = Array(Float64, 2, numelems(x) * numelems(y))
    results = Any[]
    println("num in product args", numelems(x) * numelems(y))
    i = 1
    for args in Iterators.product(D,E)
      xi = IntervalDisj(args[1])
      yi = IntervalDisj(args[2])
      res  = f(xi,yi)
      push!(results,res)
#       @show res
      i = i + 1
    end
    ⊔(results)
  end
end

function conc(f::Function, y::ConcreteReal, x::IntervalDisj)
  D = [f(y,IntervalDisj(x.intervals[:,i])) for i = 1:size(x.intervals,2)]
  ⊔(D)
end

function conc(f::Function, x::IntervalDisj, y::ConcreteReal)
  D = [f(IntervalDisj(x.intervals[:,i]),y) for i = 1:size(x.intervals,2)]
  ⊔(D)
end

convert{T<:Real}(::Type{Interval}, i::Vector{T}) = Interval(i[1],i[2])
convert(::Type{IntervalDisj}, i::Interval) = IntervalDisj([i.l,i.u])

promote_rule(::Type{Interval}, ::Type{IntervalDisj}) = IntervalDisj
promote_rule{T<:ConcreteReal}(::Type{T}, ::Type{IntervalDisj}) = Interval

## =======
## Merging
# TODO, currently no real mergin goin on'
⊔(x::IntervalDisj) = x
⊔(x::IntervalDisj, y::IntervalDisj) = IntervalDisj(hcat(x.intervals,
                                                        y.intervals))
⊔(x::IntervalDisj, y::Interval) = IntervalDisj(hcat(x.intervals, [y.l,y.u]))
⊔{T}(xs::Vector{T}) = reduce(⊔,xs)

## =============
## Set operations
#TODO - Not the same as lifting arithmetic because these are set operations
#idsubsumes(x::IntervalDisj, y::IntervalDisj) = y[1,1] >= x[1,1] && y[2,1] <= x[2,1]
overlap(x::IntervalDisj, y::IntervalDisj) = y[1,1] < x[2,1] && x[1,1] < y[2,1]

## ==========
## Arithmetic

gt(x::IntervalDisj, y::IntervalDisj) = if overlap(x,y) TF elseif x[1,1] > y[2,1] T else F end
lt(x::IntervalDisj, y::IntervalDisj) = if overlap(x,y) TF elseif x[2,1] < y[1,1] T else F end

gt(x::IntervalDisj, y::ConcreteReal) = if x[1,1] > y true elseif x[2,1] > y >= x[1,1] TF else false end
gt(y::ConcreteReal, x::IntervalDisj) =  if x[2,1] < y true elseif x[1,1] < y <= x[2,1] TF else false end

lt(x::IntervalDisj, y::ConcreteReal) = y > x
lt(y::ConcreteReal, x::IntervalDisj) = x > y

lte(x::IntervalDisj, y::IntervalDisj) = !(x > y)
gte(x::IntervalDisj, y::IntervalDisj) = !(x < y)
lte(x::IntervalDisj, y::ConcreteReal) = !(x > y)
lte(y::ConcreteReal, x::IntervalDisj) = !(y > x)

gte(x::IntervalDisj, y::ConcreteReal) = !(x < y)
gte(y::ConcreteReal, x::IntervalDisj) = !(x < y)
plus(x::IntervalDisj, y::IntervalDisj) = IntervalDisj(x[1,1] + y[1,1], x[2,1] + y[2,1])
minus(x::IntervalDisj, y::IntervalDisj) = IntervalDisj(x[1,1] - y[2,1], x[2,1] - y[1,1])
plus(x::IntervalDisj, y::ConcreteReal) = IntervalDisj(x[1,1] + y, x[2,1] + y)
plus(y::ConcreteReal, x::IntervalDisj) = x + y
minus(x::IntervalDisj, y::ConcreteReal) = IntervalDisj(x[1,1] - y, x[2,1] - y)
minus(y::ConcreteReal, x::IntervalDisj) = IntervalDisj(y - x[1,1], y - x[2,1])

mul(x::IntervalDisj, y::ConcreteReal) = IntervalDisj(x[1,1] * y, x[2,1] * y)
mul(y::ConcreteReal, x::IntervalDisj) = x * y

ijsqrt(x::IntervalDisj) = IntervalDisj(sqrt(x.l), sqrt(x.u))
function ijsqr(x::IntervalDisj)
  a,b,c,d = x[1,1] * x[1,1], x[1,1] * x[2,1], x[2,1] * x[1,1], x[2,1] * x[2,1]
  IntervalDisj(max(min(a,b,c,d),0),max(a,b,c,d,0))
end

function mul(x::IntervalDisj, y::IntervalDisj)
  a,b,c,d = x[1,1] * y[1,1], x[1,1] * y[2,1], x[2,1] * y[1,1], x[2,1] * y[2,1]
  IntervalDisj(min(a,b,c,d),max(a,b,c,d))
end

function iddiv(x::IntervalDisj, y::IntervalDisj)
  a,b,c,d = x[1,1],x[2,1],y[1,1],y[2,1]
  if !(c <= 0 <= d)
    x * IntervalDisj(1/d,1/c)
  elseif (a <= 0 <= b)
    IntervalDisj(-Inf,Inf)
  elseif b < 0 && c < d == 0
    IntervalDisj(b/c,Inf)
  elseif b < 0 && c < 0 < d
    IntervalDisj(-Inf,b/d) ⊔ IntervalDisj(b/c,Inf)
  elseif b < 0 && 0 == c < d
    IntervalDisj(-Inf,b/d)
  elseif 0 < a && c < d == 0
    IntervalDisj(-Inf,a/c)
  elseif 0 < a && c < 0 < d
    IntervalDisj(-Inf,a/c) ⊔ IntervalDisj(a/d,Inf)
  elseif 0 < a && 0 == c < d
    IntervalDisj(a/d, Inf)
  else
    Inf
  end
end

in(c::ConcreteReal, y::IntervalDisj) = y.l <= c <= y.u
inv(x::IntervalDisj) = IntervalDisj(1/x.u,1/x.l)

flip(x::IntervalDisj) = IntervalDisj(-x.l,-x.u)
lower_bound_at(x::IntervalDisj, lower_bound) = IntervalDisj(max(x.l,0), max(x.u,0))

function abs(x::IntervalDisj)
  if x.l >= 0.0 && x.u >= 0.0 x
  elseif x.u >= 0.0 IntervalDisj(0,max(abs(x.l), abs(x.u)))
  else lower_bound_at(flip(x),0.0)
  end
end

disj_to_prim =
  [:+ => :plus, :- => :minus, :* => :mul, :> => :gt, :>= => :gte,
   :<= => :lte, :< => :lt, :/ => iddiv]

for op = (:+, :-, :*, :>, :>=, :<=, :<, :/)
  idop = disj_to_prim[op]
  @eval begin
    ($op)(x::IntervalDisj,y::IntervalDisj) = ⊔(crossdisj(($idop), x,y))
  end

  @eval begin
    ($op)(y::ConcreteReal,x::IntervalDisj) = ⊔(conc(($idop), y,x))
  end

  @eval begin
    ($op)(x::IntervalDisj, y::ConcreteReal) = ⊔(conc(($idop), x,y))
  end
end

⊔(b::Bool) = b

## Discrete Distribution Hack
⊔(a::ConcreteReal, b::ConcreteReal) = IntervalDisj(a,a) ⊔ IntervalDisj(b,b)
⊔{R<:ConcreteReal}(a::Vector{R}, b::Vector{R}) = [⊔(a[i],b[i]) for i = 1:length(a)]
⊔{T,R}(a::Array{T}, b::Array{R}) = map((a,b)->⊔(a,b),a,b)

## Measure
measure(ij::IntervalDisj) = sum([ij.intervals[2,i] - ij.intervals[1,i] for i = 1:size(ij.intervals,2)])
## IntervalDisj arithmetic

# =============
# Example
A = [0 7
     5 8]
B = [9 10 10
     11 12 30]

X = Sigma.IntervalDisj(A)
Y = Sigma.IntervalDisj(B)
X * Y
X / Y

function convert(::Type{NDimBox}, ijs::Vector{IntervalDisj})
#   @show ijs
  intervals = Array(Float64,2,length(ijs))
  for j in 1:length(ijs)
    intervals[:,j] = [ijs[j][1,1] ijs[j][2,1]]
  end
  NDimBox(intervals)
end
# ⊔(X,Y)

# Printing
# string(x::IntervalDisj) = [0x0 => "{T}", 0x1 => "{F}", 0x2 => "{T,F}"][x.v]
# print(io::IO, x::IntervalDisj) = print(io, string(x))
# show(io::IO, x::IntervalDisj) = print(io, string(x))
# showcompact(io::IO, x::IntervalDisj) = print(io, string(x))
