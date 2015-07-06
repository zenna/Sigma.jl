using Sigma
using Base.Test

# Should be able to sample from any distribution
function cansample(X::RandVar; nsamples = 100)
  samples = rand(X, nsamples)
  @test typeof(samples) == Vector{rangetype(X)}
  @test length(samples) == nsamples
  return true
end

# Should be able to sample from any distribution
function test_randvar(X::RandVar)
  @test cansample(X)
end

randvars = [
  uniform(1, 0, 1),
  uniform(0, 1),
  exponential(0.5),
  exponential(1,0.5),
  logistic(1.0,1.0)]

for randvar in randvars
  println("Testing $(randvar)")
  test_randvar(randvar)
end

## Test Arithmetic
## ===============

## Goal is to test real valued 
for op in (+,-,/,*,^)
  for r1 in randvars, r2 in randvars
    println("Testing $op($r1, $r2)")
    test_randvar(op(r1, r2))
  end
end

real_floating = [exp,log,sin,
  cos,tan,asin,
  acos,atan,sinh,
  cosh,tanh,atan2]

for op in real_floating
  for r in RandVar
    println("Testing $op($r)")
    test_randvar(op(r))
  end
end