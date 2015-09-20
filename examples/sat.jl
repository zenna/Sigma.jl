# Probabilistic Inference Generalises Boolean SATisfiability

using Sigma
using Base.Test

A = Sigma.flip()
B = Sigma.flip(0.9)
C = Sigma.flip()

a, b, c = rand((A, B, C), !A & !B & !C)
@test !a & !b & !c

a, b, c = rand((A, B, C), (A & B) | C)
@test (a & b) | c

a, b, c = rand((A, B, C), (A & B) | !C & A)
@test (a & b) | !c & a
