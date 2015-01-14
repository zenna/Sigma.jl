using Sigma

# Probabilistic Programming Generalises SMT

X = uniform(0,10)
Y = uniform(0,10)
Z = uniform(0,10)

formula = 3X + 2Y - Z >= 4
vars = MakeRandomArray([X,Y,Z])
solutions = cond(vars,formula)
model = rand(solutions)

