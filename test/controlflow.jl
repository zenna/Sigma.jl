using Base.Test
import Sigma: @If, @While, Interval, TF, Omega, flip

# Should act like a normal if when cond is true
begin
  local x = 0
  local a = @If x > 0 false true
  @test a
  local b = @If x == 0 true false
  @test b
end

# When condition is TF, we should explore and merge both branches
begin
  local x = TF
  local a = @If x false true
  @test a === TF
  a = ifelse(x, false, true)
  @test a === TF

  # @If should short-circuit
  local m = 0.0
  a = @If true m (m += 1;m)
  @test m == 0.0

  a = ifelse(true,m,(m += 1;m))
  @test m == 1.0
end

# When cond is a random variable, @If and ifelse return a random variable
begin
  local x = flip(1,0.6)
  local a = @If x false true
  @test isa(a,Sigma.RandVar)
  @test a(Omega()) === TF
  @test a([0.3]) == false
  @test a([0.7]) == true

  a = ifelse(x,false,true)
  @test isa(a,Sigma.RandVar)
  @test a(Omega()) === TF
  @test a([0.3]) == false
  @test a([0.7]) == true
end

# When cond is random variable, and a/b also random variable
# @If and ifelse should return random variable which "pipes"
# input to consequent and/or alternative.
begin
  local x = flip(1,0.6)
  local a = @If x flip(1,0.9) flip(1,0.2)
  @test isa(a,Sigma.RandVar)
  # Omega() should be piped through to a or b, and hence:
  @test !isa(a(Omega()),Sigma.RandVar)
  @test a([0.3]) == true
  @test a([0.7]) == false

  a = ifelse(x,flip(1,0.9), flip(1,0.2))
  @test isa(a,Sigma.RandVar)
  # Omega() should be piped through to a or b, and hence:
  @test !isa(a(Omega()),Sigma.RandVar)
  @test a([0.3]) == true
  @test a([0.7]) == false
end

begin
  local x = Interval(-5,-2)
  @While(x < 0,
    begin
      x = x + 1
    end)
  @test x == Interval(0,3)
end
