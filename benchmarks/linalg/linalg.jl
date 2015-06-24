using Sigma

m = 3
n = 3
A = Sigma.mvuniform(-1,1,m,n)

# Sample matrix whose sum is 3
As = rand(A, sum(A) == 3)
sum(As)

# Sample Orthogonal Matrix
As = rand(A, (A'*A == eye(m,n)), 1)
As * As'

# trace
B = Sigma.mvexponential(0.5, m, n)
C = Sigma.mvlogistic(1, 1, m, n)

Bs, Cs = rand((B,C), (trace(B) == trace(C)), 1)
trace(Bs[1])
trace(Cs[1])