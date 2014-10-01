using Sigma
using Base.Test
Xs = RandomArray(Float64,3,4)
@test length(Xs(Omega())) == 12

Xs2 = setindex(Xs,99,1,2)
Xs2(Omega())
@test Xs2(Omega())[1,2] == 99

Xs3 = setindex(Xs2, uniform(0,0,2), 2, 2)
@test Xs3(Omega())[2,2] == Interval(0,2

Xs4 = independentRandomArray(x->uniform(x,0,1),2,2)
@test Xs4(Omega())[1] == Interval(0,1)
@test prob_deep(sum(Xs) < 2)[2] < 0.6
