using Sigma
using Base.Test

# Probabilistic Programming Generalises SAT
A = flip()
B = flip()
C = flip()

formula = (A & B) | C
a,b,c = rand([A,B,C], solutions)
@test (a & b) | c