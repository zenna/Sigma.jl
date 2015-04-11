## Meta (Hybrid, Portoflio) RandomVariable
## =======================================

# Different kinds of random variable are good at different things
# RandVarMeta tries to have its cake and eat it

type RandVarMeta{T} <: RandVar{T}
  smt::RandVarSMT{T}
  ai::RandVarAI{T}
end

## Distribution
## ============
flipmeta(i,p) = RandVarMeta(flipsmt(i,p),flipai(i,p))
flipmeta(p) = (g = genint(); RandVarMeta(flipsmt(g,p),flipai(g,p)))

uniformmeta(i,a,b) = RandVarMeta(uniformsmt(i,a,b),uniformai(i,a,b))
uniformmeta(a,b) = (g = genint(); RandVarMeta(uniformsmt(g,a,b),uniformai(g,a,b)))

discreteuniformmeta(i,a,b) = RandVarMeta(discreteuniformsmt(i,a,b),
                                         discreteuniformai(i,a,b))
discreteuniformmeta(a,b) = discreteuniformmeta(genint(), a,b)

rand(X::RandVarMeta) = rand(X.ai) # Default AI
call(X::RandVarMeta, o;args...) = call(X.ai,o; args...) # Default AI

call(X::RandVarMeta{Bool}, o::SampleOmega; args...) = call(X.ai,o; args...) # Default SMT
call(X::RandVarMeta{Bool}, o;  args...) = call(X.smt,o;  args...) # Default SMT
call(X::RandVarMeta, o::SampleOmega;  args...) = call(X.ai,o; args...) # Default SMT

checksat(f::RandVarMeta,Y,X::Domain;  args...) = checksat(f.smt,Y,X;  args...) # Default SMT

# Binary functions, with Real output
for op = (:+, :-, :*, :/, :>, :>=, :<=, :<, :(==), :!=, :isapprox, :&, :|, :(==), :!=)
  @eval begin
    function ($op)(X::RandVarMeta, Y::RandVarMeta)
      let op = $op
        RandVarMeta(($op)(X.smt, Y.smt),($op)(X.ai, Y.ai))
      end
    end

    ($op){T1<:Real, T2<:Real}(X::RandVarMeta{T1}, c::T2) =
      RandVarMeta(($op)(X.smt,c),($op)(X.ai,c))
    ($op){T1<:Real, T2<:Real}(c::T1, X::RandVarMeta{T2}) =
      RandVarMeta(($op)(c,X.smt),($op)(c,X.ai,))
  end
end

# Unary functions
for op = (:!, :sqr,:abs, :sqrt, :round)
  @eval begin
    function ($op)(X::RandVarMeta)
      let op = $op
        RandVarMeta(($op)(X.smt),($op)(X.ai))
      end
    end
  end
end

smt(x) = x
smt(x::RandVarMeta) = x.smt
ai(x) = x
ai(x::RandVarMeta) = x.ai

function ifelse(A::RandVarMeta,B,C)
  RandVarMeta(ifelse(A.smt,smt(B),smt(C)),ifelse(A.ai,ai(B),ai(C)))
end

# # Interop with RandVarSMT
# function ifelse(A::RandVarSMT, B::RandVarMeta, C::RandVarMeta)
#   @assert rangetype(B) == rangetype(C)
#   newast = :(ite($(ast(A)),$(ast(B.smt)),$(ast(C.smt))))
#   RandVarSMT{rangetype(B)}(newast, union(A.assert_gens, B.smt.assert_gens, C.smt.assert_gens),
#                    union(A.dims, B.smt.dims, C.smt.dims))
# end

# function ifelse(c::RandVarAI{Bool},x::RandVarMeta,y::RandVarMeta)
#   @assert rangetype(x) == rangetype(y)
#   RandVarAI(rangetype(x),:(ifelse(call($c,ω),pipeomega($(x.ai),ω),pipeomega($(y.ai),ω))))
# end

mvuniformmeta(a,b, i::Int, j::Int) = iidmeta(Float64, c->uniformmeta(a,b),i,j)
mvuniformmeta(a,b, i::Int) = iidmeta(Float64, c->uniformmeta(a,b),i)

mvnormalmeta(μ,σ, i::Int, j::Int) = iidmeta(Float64, c->normalmeta(μ,σ),i,j)
mvnormalmeta(μ,σ, i::Int) = iidmeta(Float64, c->normalmeta(μ,σ),i)

rangetype(X::RandVarMeta) = typeof(X).parameters[1]
