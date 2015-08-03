using Base.Test
using Sigma
import Sigma: LazyOmega, flip

# When cond is a random variable, @If and ifelse return a random variable
begin
  local x = flip(0.6)
  local a = ifelse(x,false,true)
  @show typeof(a)
  @test isa(a,Sigma.RandVar)
  @test call(a,LazyOmega()) === tf
  @test call(a,[0.3]) == false
  @test call(a,[0.7]) == true

  a = ifelse(x,false,true)
  @test isa(a,Sigma.RandVar)
  @test call(a,LazyOmega()) === tf
  @test call(a,[0.3]) == false
  @test call(a,[0.7]) == true
end

# When cond is random variable, and a/b also random variable
# @If and ifelse should return random variable which "pipes"
# input to consequent and/or alternative.
begin
  local x = flip(0.6)
  local a = ifelse(x,flip(0.9),flip(0.2))
  @test isa(a,Sigma.RandVar)
  # LazyOmega() should be piped through to a or b, and hence:
  @test !isa(call(a,LazyOmega()),Sigma.RandVar)
  @test call(a,[0.3]) == true
  @test call(a,[0.7]) == false

  a = ifelse(x,flip(0.9), flip(0.2))
  @test isa(a,Sigma.RandVar)
  # LazyOmega() should be piped through to a or b, and hence:
  @test !isa(call(a,LazyOmega()),Sigma.RandVar)
  @test call(a,[0.3]) == true
  @test call(a,[0.7]) == false
end
