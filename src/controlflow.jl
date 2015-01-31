# When condition is TF we need to evaluate both branches
# and merge with ⊔
function ifelse(c::AbstractBool, x, y)
  if c === T
    x
  elseif c === F
    y
  elseif c === TF
    ⊔(x,y)
  end
end

# When cond is a random variable, @If and ifelse return a random variable
# Which also 'pipes' ω into x and y if they are random variables
function ifelse{T}(c::RandVar{Bool},x::T,y::T)
  RandVarSymbolic(rangetype(x),:(ifelse(call($c,ω),pipeomega($x,ω),pipeomega($y,ω))))
end

# function makeif(condition::Expr, conseq::Expr, alt::Expr)
#   quote
#     a = $(esc(condition))
#     if isa(a, Bool)
#       a ? $(esc(conseq)) : $(esc(alt))
#     elseif c === T
#       $(esc(conseq))
#     elseif c === F
#       $(esc(alt))
#     elseif c === TF
#       a = $(esc(conseq))
#       b = $(esc(alt))
#       ⊔(a,b)
#     end
#   end
# end

# # Add a clause b to an ifelse block a
# function catifelse(a::Expr, b::Expr)
# end


# macro If2(a,b,c)
#   x = makeif(a,b,c)
#   rvinner = makeif(a,:(pipeomega($b,ω)),:(pipeomega($c,ω)))
#   rv =
#   quote
#     if isa($a, RandVar)
#       function(ω)
#         $rvinner
#       end
#     end
#   end
#   catifelse(x,rv)
# end

# # If a then b else c
# macro If(condition,conseq,alt)
#   quote
#     a = $(esc(condition))
#     if isa(a, Bool)
#       a ? $(esc(conseq)) : $(esc(alt))
#     elseif c === T
#       $(esc(conseq))
#     elseif c === F
#       $(esc(alt))ifelse([true,false,true],[1,2,3],[4,5,6])
# -
#     elseif c === TF
#       a = $(esc(conseq))
#       b = $(esc(alt))
#       ⊔(a,b)
#     elseif isa(a,RandVar)

#     else
#       throw(DomainError())
#     end
#   end
# end

# macro IfRV(condition,conseq,alt)
#   quote
#     function(ω)
#       @If condition pipeomega(conseq,ω) pipeomega(alt,ω)
#   end
# end




#     if isa(d, Bool)
#       d ? pipeomega($(esc(conseq)),ω) : pipeomega($(esc(alt)),ω)
#     elseif d === T
#       pipeomega($(esc(conseq)),ω)
#     elseif d === F
#       pipeomega($(esc(alt)),ω)
#           elseif d === TF
#             a = pipeomega($(esc(conseq)),ω)
#             b = pipeomega($(esc(alt)),ω)
#             ⊔(a,b)
#           else
#             println("condition is " , d)
#             throw(DomainError())

# Short circut version of ifelse, handles AbstractBool and RandVar
macro If(condition, conseq, alt)
  local idtrue = singleton(gensym())
  local idfalse = singleton(gensym())
  q =
  quote
  c =  $(esc(condition));
#   println("enterin$$g the if",$idtrue)
  if isa(c, RandVar)
    (ω)->begin
          d = c(ω)
          if isa(d, EnvVar)
            ret = EnvVar()
            for world in d.worlds
              if world[2] === T || world[2] === true
                ret.worlds[world[1]] = pipeomega($(esc(conseq)),ω)
              elseif world[2] === F || world[2] === false
                ret.worlds[world[1]] = pipeomega($(esc(alt)),ω)
              elseif world[2] === TF
                a = pipeomega($(esc(conseq)),ω)
                constraintstrue = union(world[1],$idtrue)
                update_ret!(a,ret, constraintstrue)

                b = pipeomega($(esc(alt)),ω)
                constraintsfalse = union(world[1],$idfalse)
                update_ret!(b,ret, constraintsfalse)

              else
                println("error:", world[2])
                throw(DomainError())
              end
            end
          elseif isa(d, Bool)
            d ? pipeomega($(esc(conseq)),ω) : pipeomega($(esc(alt)),ω)
          elseif d === T
            pipeomega($(esc(conseq)),ω)
          elseif d === F
            pipeomega($(esc(alt)),ω)
          elseif d === TF
            a = pipeomega($(esc(conseq)),ω)
            b = pipeomega($(esc(alt)),ω)
            ⊔(a,b)
          else
            println("condition is " , d)
            throw(DomainError())
          end
        end

  elseif isa(c, EnvVar)
    ret = EnvVar()
    for world in c.worlds
#       @show world[2]
#       println("length=", length(c.worlds))
      if world[2] === T || world[2] === true
        v = $(esc(conseq))
        update_ret!(v,ret, world[1])

#                 println("DID I FIND YOU BITCH?")
#         ret.worlds[world[1]] = $(esc(conseq))
#                     println("NOO YOU BITCH?")

      elseif world[2] === F || world[2] === false
#             println("DID I FIND YOU BITCH?")
        v = $(esc(alt))
        update_ret!(v,ret, world[1])

#         println("LETS SEE BITCH")
#         @show v
#         ret.worlds[world[1]] = v
#         println("NO BITCH?")
      elseif world[2] === TF
        a = $(esc(conseq))
        constraintstrue = union(world[1],$idtrue)
        update_ret!(a,ret, constraintstrue)

        b = $(esc(alt))
        constraintsfalse = union(world[1],$idfalse)
        update_ret!(b,ret, constraintsfalse)
#         println("leaving")
      else
        println("error:", world[2])
        throw(DomainError())
      end
    end
  elseif isa(c, Bool)
    c ? $(esc(conseq)) : $(esc(alt))
  elseif c === T
    $(esc(conseq))
  elseif c === F
    $(esc(alt))
  elseif c === TF
    a = $(esc(conseq))
    b = $(esc(alt))
    ⊔(a,b)
  else
    throw(DomainError())
  end
#   println("leaving the if", $idtrue)
  end
  return q
end

# REVIEW: IS THIS STILL RELEVANT? TEST OR REMOVE
macro While(c, todo)
  quote
    while $(esc(c)) === true || $(esc(c)) === T || $(esc(c)) === TF
      $(esc(todo));
    end
  end
end
