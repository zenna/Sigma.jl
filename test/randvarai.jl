using Base.Test
using Sigma
import Sigma: normalai, uniformai, gammaai, random, betarvai
import Sigma: categoricalai, geometricai, poissonai, discreteuniformai
import Sigma: flipai

## Real valued RandVarAis
real_rvs = [random(1),normalai(0,1), uniformai(0,10),gammaai(0.1,0.9),
       betarvai(0.5,0.5)]

## Test to see arithmetic is working
for i in real_rvs, j in real_rvs
  for op in (+,-,*)
    x = op(i,j)
    @test rangetype(x) == Float64
    rand(x)
    prob(x>rand())

    y = ifelse(flipai(rand()),i,j)
    @test rangetype(y) == Float64
    rand(y)
    prob(y>rand())
  end
end

## Int Rvs
int_rvs = [categoricalai([.2,.3,.4,.1]), geometricai(0.5), poissonai(.5),
           discreteuniformai(0,10)]

for i in int_rvs, j in int_rvs
  for op in (+,-,*)
    x = op(i,j)
    @test rangetype(x) == Int
    rand(x)
    prob(x>rand())

    y = ifelse(flipai(rand()),i,j)
    @test rangetype(y) == Int
    rand(y)
    prob(y>rand())
  end
end

## TODO: Test division/ifelse
rand(ifelse(flipai(),uniformai(0,1),normalai(0,1)))