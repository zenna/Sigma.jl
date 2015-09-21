using Sigma
using Base.Test

X = uniform(0,10)
Y = uniform(0,10)
Z = uniform(0,10)

formula = 3X + 2Y - Z >= 4
x,y,z = rand((X, Y, Z), formula)
@test 3x + 2y - z >= 4
@test 0 < x < 10
@test 0 < y < 10
@test 0 < z < 10
