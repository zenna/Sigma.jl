using Sigma
using Lens

srand(1234)

# Paramter Estimation
λ = uniform(0,2)
x = mvexponential(λ, 3)
observations = x == [0.083, 0.55, 2.37]
rand(λ, observations)
rand(x, observations)

m = 3
n = 3
A = Sigma.mvuniform(-1,1,m,n);

# Sample matrix whose sum is 3
As = rand(A, sum(A) == 3)
sum(As)

# Sample Orthogonal Matrix
orthogonal_A = rand(A, (A'*A == eye(m,n)))
orthogonal_A * orthogonal_A'
map(round, orthogonal_A * orthogonal_A')

# trace
B = mvexponential(0.5, m, n);
C = mvlogistic(1, 1, m, n);

Bs, Cs = rand((B,C), (trace(B) == trace(C)), 1)
trace(Bs[1])
trace(Cs[1])

# Simple
A = uniform(0,1)
B = exponential(.5)
rand(A, A^2/sin(A) > 0.45 * atan(B))
rand(A, A < -1)

## Non Negative Matrix Factorisation
## ==================================
dist(A,B; epsilon = 1.0) = sum([(A[i] - B[i])^2 for i = 1:length(A)]) < epsilon

function nmf(V, W, H)
  dist(V, W*H)
end

W = mvuniform(0.0,10.0,4,2)
H = mvuniform(0.0,10.0,2,4)
V = rand(4,4)

nmf(V, W, H)
