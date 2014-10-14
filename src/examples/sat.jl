using Sigma

# Probabilistic Programming Generalises SAT

A = flip()
B = flip()
C = flip()
E = flip()

formula = (A & B) | C
vars = MakeRandomArray([A,B,C])
solutions = cond(vars,formula)
model = rand(solutions)
model[1],model[2],model[3]