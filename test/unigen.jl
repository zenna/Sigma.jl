using Sigma
a = flip(1,0.1)
b = flip(2,0.2)
c = flip(3,0.3)
d = flip(4,0.4)

e = (a | b) & (c | d)
cnf = Sigma.analyze(e)[2]