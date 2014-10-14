immutable Interval <: Domain{Real}
  l::Real
  u::Real
  Interval(l,u) =  if u > l new(l, u) else new(u,l) end
end

Interval(v::Vector) = Interval(v[1],v[2])
unitinterval() = Interval(0.,1.)

## ===========
## Conversions

function convert(::Type{NDimBox}, i::Vector{Interval})
  intervals = Array(Float64,2,length(i))
  for j in 1:length(i)
    intervals[:,j] = [i[j].l i[j].u]
  end
  NDimBox(intervals)
end
convert(::Type{Vector{Interval}}, b::NDimBox) = [Interval(b.intervals[:,i]) for i = 1:num_dims(b)]

# A concrete number can be concerted to an interval with no width
convert(::Type{Interval}, c::ConcreteReal) = Interval(c, c)
promote_rule{T<:ConcreteReal}(::Type{T}, ::Type{Interval}) = Interval

## Set operations
## ==============

num_dims(i::Interval) = 1
subsumes(x::Interval, y::Interval) = y.l >= x.l && y.u <= x.u
overlap(x::Interval, y::Interval) = y.l <= x.u && x.l <= y.u

## ====================================
## Interval Arithmetic and Inequalities

function eq(x::Interval, y::Interval)
  if x.u == y.u && x.l == y.l T
  elseif overlap(x,y) TF
  else F end
end

neq(x::Interval,y::Interval) = !(eq(x,y))

eq(x::Interval,y::ConcreteReal) = eq(promote(x,y)...)
eq(y::ConcreteReal,x::Interval) = eq(promote(y,x)...)

neq(x::Interval, y::ConcreteReal) = !eq(x,y)
neq(y::ConcreteReal, x::Interval) = !eq(y,x)

>(x::Interval, y::Interval) = if overlap(x,y) TF elseif x.l > y.u T else F end
<(x::Interval, y::Interval) = if overlap(x,y) TF elseif x.u < y.l T else F end

>(x::Interval, y::ConcreteReal) = if x.l > y true elseif x.u > y >= x.l TF else false end
>(y::ConcreteReal, x::Interval) =  if x.u < y true elseif x.l < y <= x.u TF else false end

<(x::Interval, y::ConcreteReal) = y > x
<(y::ConcreteReal, x::Interval) = x > y

<=(x::Interval, y::Interval) = !(x > y)
>=(x::Interval, y::Interval) = !(x < y)
<=(x::Interval, y::ConcreteReal) = !(x > y)
<=(y::ConcreteReal, x::Interval) = !(y > x)

>=(x::Interval, y::ConcreteReal) = !(x < y)
>=(y::ConcreteReal, x::Interval) = !(x < y)
+(x::Interval, y::Interval) = Interval(x.l + y.l, x.u + y.u)
-(x::Interval, y::Interval) = Interval(x.l - y.u, x.u - y.l)
+(x::Interval, y::ConcreteReal) = Interval(x.l + y, x.u + y)
+(y::ConcreteReal, x::Interval) = x + y
-(x::Interval, y::ConcreteReal) = Interval(x.l - y, x.u - y)
-(y::ConcreteReal, x::Interval) = Interval(y - x.l, y - x.u)

*(x::Interval, y::ConcreteReal) = Interval(x.l * y, x.u * y)
*(y::ConcreteReal, x::Interval) = x * y

sqrt(x::Interval) = Interval(sqrt(x.l), sqrt(x.u))

# CODEREVIEW: Generalise to even powers
function sqr(x::Interval)
  a,b,c,d = x.l * x.l, x.l * x.u, x.u * x.l, x.u * x.u
  Interval(max(min(a,b,c,d),0),max(a,b,c,d,0))
end

function *(x::Interval, y::Interval)
  a,b,c,d = x.l * y.l, x.l * y.u, x.u * y.l, x.u * y.u
  Interval(min(a,b,c,d),max(a,b,c,d))
end

# is c inside the interval
# CODREVIEW: TESTME
in(c::ConcreteReal, y::Interval) = y.l <= c <= y.u

# CODREVIEW: TESTME
inv(x::Interval) = Interval(1/x.u,1/x.l)

# Ratz Interval Division
# CODREVIEW: TESTME
function /(x::Interval, y::Interval)
  a,b,c,d = x.l,x.u,y.l,y.u
  if !(0 ∈ y)
    x * inv(y)
  elseif (0 ∈ x)
    Interval(-Inf,Inf)
  elseif b < 0 && c < d == 0
    Interval(b/c,Inf)
  elseif b < 0 && c < 0 < d
    Interval(-Inf,Inf)
  elseif b < 0 && 0 == c < d
    Interval(-Inf,b/d)
  elseif 0 < a && c < d == 0
    Interval(-Inf,a/c)
  elseif 0 < a && c < 0 < d
    Interval(-Inf,Inf)
  elseif 0 < a && 0 == c < d
    Interval(a/d, Inf)
  else
    Inf
  end
end

/(c::ConcreteReal, x::Interval) = convert(Interval,c) / x
/(x::Interval, c::ConcreteReal) = x / convert(Interval,c)

flip(x::Interval) = Interval(-x.l,-x.u)
makepos(x::Interval) = Interval(max(x.l,0), max(x.u,0))

function abs(x::Interval)
  if x.l >= 0.0 && x.u >= 0.0 x
  elseif x.u >= 0.0 Interval(0,max(abs(x.l), abs(x.u)))
  else makepos(flip(x))
  end
end

round(x::Interval) = Interval(round(x.l), round(x.u))

## =======
## Merging

function ⊔(a::Interval, b::Interval)
  l = min(a.l,b.l)
  u = max(a.u, b.u)
  Interval(l,u)
end

⊔(a::Interval, b::ConcreteReal) = ⊔(promote(a,b)...)
⊔(b::ConcreteReal, a::Interval) = ⊔(promote(b,a)...)
⊔(a::Interval) = a

## ========
## Splitting
function split_box(i::Interval, split_point::Float64)
  @assert i.l <= split_point <= i.u "Split point must be within interval"
  @assert i.l != i.u "Can't split a single point interval into disjoint sets"

  if split_point < i.u
    [Interval(i.l, split_point), Interval(nextfloat(split_point), i.u)]
  else
    [Interval(i.l, prevfloat(split_point)), Interval(split_point, i.u)]
  end
end

# middle_split(is::Vector{Interval}) = map(to_intervals,middle_split(convert(NDimBox, is,)))
measure(i::Interval) = i.u - i.l
findnext
