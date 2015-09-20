# Probabilistic Inference Generalises Boolean SATisfiability

using Sigma
using Base.Test

A = Sigma.flip()
B = Sigma.flip()
C = Sigma.flip()

a, b, c = rand((A, B, C), A! & !B & !C, 1)
@test !a & !b & !c


formula = (A & B) | C
a, b, c = rand((A, B, C), formula, 1)
@show a, b, c
@test (a[1] & b[1]) | c[1]
