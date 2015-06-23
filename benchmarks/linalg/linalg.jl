using Sigma

m = 3
n = 3
A = Sigma.mvuniform(-1,1,m,n)

# Sample matrix whose sum is 3
rand(A,sum(A) == 3)

# Sample Orthogonal Matrix
sample = rand(A, (A'*A == eye(m,n)), 1)

# Factorise
col = Sigma.mvexponential(0.5,m)
row = Sigma.mvlogistic(1,1,m)


A = Sigma.mvuniform(-10,10,3,2)
B = Sigma.mvuniform(-10,10,2,3)

data = [1. 2 0
        4 1 6
        7 3 2]

result = rand((A,B), A*B == data,1)

rowsample = result[1][1]
colsample = result[2][1]
colsample * rowsample.'
