# Variables which can be multiple values
NotEnv = Union(Float64, Bool, AbstractBool, Array, Int64, Interval)
immutable EnvVar{K,V}
  worlds::Dict{K,NotEnv}

  EnvVar() = new(Dict{K,V}())
  EnvVar(worlds::Dict{K,V}) = new(worlds)
end
EnvVar() = EnvVar{Any,Any}()
singleton{T}(x::T) = (s = Set{T}();push!(s,x);s)
const noconstraints = Set{Symbol}()

typealias IntervalEnvDict Dict{Set{Symbol},Interval}
typealias IntervalEnvVar EnvVar{Set{Symbol}, Interval}

function intervalenvvar{T<:Real}(x::T,y::T)
  EnvVar{Set{Symbol},Interval}(IntervalEnvDict([noconstraints => Interval(x,y)]))
end

unitinterval(::Type{EnvVar}) = intervalenvvar(0.,1.)

function getindex(e::EnvVar, i::Int64)
  ret = EnvVar()
  for world in e.worlds
    val = world[2][i]
    if isa(val, EnvVar)
      for valworld in val.worlds
        ret.worlds[valworld[1]] = valworld[2]
      end
    else
      ret.worlds[world[1]] = world[2][i]
    end
  end
  ret
end

function getindex(e::EnvVar, i::Int64, j::Int64)
  ret = EnvVar()
  for world in e.worlds
    val = world[2][i,j]
    if isa(val, EnvVar)
      for valworld in val.worlds
        ret.worlds[valworld[1]] = valworld[2]
      end
    else
      ret.worlds[world[1]] = world[2][i,j]
    end
  end
  ret
end


# function getindex(e::EnvVar, i::Int64, j::Int64)
#   ret = EnvVar()
#   for world in e.worlds
#     ret.worlds[world[1]] = world[2][i,j]
#   end
#   ret
# end

# Set functions
function subsumes(a::AbstractBool,e::EnvVar)
  doessubsume = true
  for world in e.worlds
    doessubsume = doessubsume & subsumes(a,world[2])
  end
  doessubsume
end

function convert(::Type{Vector{EnvVar}}, b::HyperBox)
  x = [intervalenvvar(b.intervals[1,i],b.intervals[2,i]) for i = 1:num_dims(b)]
end

function overlap(e::EnvVar, a::AbstractBool)
  doesoverlap = false # only has to overlap with one
  for world in e.worlds
    doesoverlap = doesoverlap | overlap(a,world[2])
  end
  doesoverlap
end

function overlap(a::AbstractBool, e::EnvVar)
  doesoverlap = false # only has to overlap with one
  for world in e.worlds
    doesoverlap = doesoverlap | overlap(a,world[2])
  end
  doesoverlap
end

ConcreteValue = Union(Float64, Int64, Bool)

#FIXME, IVE GOT IN and SIZE AS ASSOCIATE BUT ITS NOT
for op = (:+, :-, :*, :>, :>=, :<=, :<, :&, :|, :in, :/, :size)
  @eval begin
    function ($op)(x::EnvVar, y::EnvVar)
      ret = EnvVar() #FIXME: MAKE TYPE STABLE
      for xworld in x.worlds
        xworldid = xworld[1]
        if haskey(y.worlds,xworldid)     # If we share the same world
          ret.worlds[xworldid] = ($op)(xworld[2],y.worlds[xworldid])
        else
          for yworld in y.worlds
            conjworld = union(xworldid,yworld[1])
            ret.worlds[conjworld] = ($op)(xworld[2],yworld[2])
          end
        end
      end
      ret
    end
  end

  @eval begin
    function ($op)(x::EnvVar, y::ConcreteValue)
      ret = EnvVar() #FIXME: MAKE TYPE STABLE
      for xworld in x.worlds
        xworldid = xworld[1]
        ret.worlds[xworldid] = ($op)(xworld[2],y)
      end
      ret
    end
  end

  @eval begin
    function ($op)(y::ConcreteValue, x::EnvVar)
      ret = EnvVar() #FIXME: MAKE TYPE STABLE
      for xworld in x.worlds
        xworldid = xworld[1]
        ret.worlds[xworldid] = ($op)(y,xworld[2])
      end
      ret
    end
  end
end

for op = (:sqr, :sqrt, :inv)
  @eval begin
    function ($op)(x::EnvVar)
      ret = EnvVar() #FIXME: MAKE TYPE STABLE
      for xworld in x.worlds
        xworldid = xworld[1]
        ret.worlds[xworldid] = ($op)(xworld[2])
      end
      ret
    end
  end
end

function update_ret!(a::EnvVar,ret::EnvVar, constraints)
  for aworld in a.worlds
    ret.worlds[union(aworld[1],constraints)] = aworld[2]
  end
end

function update_ret!(a::ConcreteValue, ret::EnvVar, constraints)
  ret.worlds[constraints] = a
end

function add_path_constraints(e::EnvVar, constraints)
  ret = EnvVar()
  for world in e.worlds
    ret.worlds[union(world[1],constraints)] = world[2]
  end
  ret
end

add_path_constraints(e::ConcreteValue, constraints) = e

function update_ret!(a::Array, ret::EnvVar, constraints)
  amap = map(x->add_path_constraints(x,constraints),a)
  ret.worlds[constraints] = amap
end

macro Iff(condition, conseq, alt)
  local idtrue = singleton(gensym())
  local idfalse = singleton(gensym())
  q =
  quote
  c =  $(esc(condition));
  local ret
  if isa(c, EnvVar)
    ret = EnvVar()
    @show world[2]
    for world in c.worlds
      if world[2] === T || world[2] === true
        ret.worlds[world[1]] = $(esc(conseq))
      elseif world[2] === F || world[2] === false
        ret.worlds[world[1]] = $(esc(alt))
      elseif world[2] === TF
        a = $(esc(conseq))
        constraintstrue = union(world[1],$idtrue)
        update_ret!(a,ret, constraintstrue)

        b = $(esc(alt))
        constraintsfalse = union(world[1],$idfalse)
        update_ret!(b,ret, constraintsfalse)

      else
        println("error:", world[2])
        throw(DomainError())
      end
    end
  end
  ret
  end
  return q
end
