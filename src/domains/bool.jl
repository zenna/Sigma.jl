# Abstract Boolean Types

immutable AbstractBool <: Domain{Bool}
  v::Uint8
  AbstractBool(v::Uint8) = (@assert v == 0x1 || v == 0x2 || v== 0x3; new(v))
end

const T = AbstractBool(0x1)
const F = AbstractBool(0x2)
const TF = AbstractBool(0x3)

promote_rule(::Type{Bool}, ::Type{AbstractBool}) = AbstractBool
convert(::Type{AbstractBool}, b::Bool) = if b T else F end

## =========================
## Lifted Boolean Arithmetic

function !(b::AbstractBool)
  if b === T
    F
  elseif b === F
    T
  elseif b === TF
    TF
  end
end

(==)(x::AbstractBool, y::AbstractBool) = x === TF || y === TF ? TF : x === T && y === T || x === F && y === F
function (==)(x::AbstractBool, y::AbstractBool)
  if x === TF || y === TF TF
  elseif x === T && y === T T
  elseif x === F && y === F T
  else F
  end
end
(==)(x::AbstractBool, y::Bool) = apply(==,promote(x,y))
(==)(y::Bool,x::AbstractBool) = apply(==,promote(y,x))

function (|)(x::AbstractBool, y::AbstractBool)
  if x === T || y === T T
  elseif x === TF || y === TF TF
  else F
  end
end
|(x::AbstractBool, y::Bool) = |(x,convert(AbstractBool,y))
|(y::Bool, x::AbstractBool) = |(convert(AbstractBool,y), x)

function (&)(x::AbstractBool, y::AbstractBool)
  if x === F || y === F F
  elseif x === TF || y === TF TF
  else T
  end
end

(&)(x::AbstractBool, y::Bool) = x & convert(AbstractBool, y)
(&)(y::Bool, x::AbstractBool) = convert(AbstractBool, y) & x

## ===========================
## AbstractBool Set Operations
subsumes(x::AbstractBool, y::AbstractBool) = x === TF || x === y
subsumes(x::AbstractBool, y::Bool) = subsumes(x,convert(AbstractBool, y))

overlap(x::AbstractBool, y::AbstractBool) = !((x === T && y === F) || (x === F && y === T))
overlap(x::AbstractBool, y::Bool) = overlap(x,convert(AbstractBool, y))
overlap(x::Bool, y::AbstractBool) = overlap(convert(AbstractBool, x),y)

⊔(a::AbstractBool) = a
⊔(a::AbstractBool, b::AbstractBool) = a === b ? a : TF
⊔(a::Bool, b::AbstractBool) = ⊔(convert(AbstractBool,a),b)
⊔(a::AbstractBool, b::Bool) = ⊔(a,convert(AbstractBool,b))
⊔(a::Bool, b::Bool) = a === b ? convert(AbstractBool,a) : TF

## ===========================
## Printing
string(x::AbstractBool) = ["{T}","{F}","{T,F}"][x.v]
print(io::IO, x::AbstractBool) = print(io, string(x))
show(io::IO, x::AbstractBool) = print(io, string(x))
showcompact(io::IO, x::AbstractBool) = print(io, string(x))
