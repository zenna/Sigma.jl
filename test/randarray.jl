using Sigma
using Base.Test

Xs = iid(Float64, random, 3,3)
@test rand(length(Xs)) == 9
@test 0 <= rand(Xs[1,1]) <= 1
@test 0 <= sum(rand(Xs)) <= 9

As = iid(Float64, random, 3,1)
Bs = iid(Float64, random, 3,1)
rand(As⋅Bs)