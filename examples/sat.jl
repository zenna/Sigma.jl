# Probabilistic Inference Generalises Boolean SATisfiability

using Sigma
using Base.Test

A = flip()
B = flip()
C = flip()

formula = (A & B) | C
a, b, c = rand((A, B, C), formula, 1)
@test (a & b) | c