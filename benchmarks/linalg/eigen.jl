## Eigen Vectors/Values
## ====================
using Sigma

dist(A,B; epsilon = 1.0) = sum([(A[i] - B[i])^2 for i = 1:length(A)]) < epsilon

dist(A,B; epsilon = 1.0) = sum([abs(A[i] - B[i]) for i = 1:length(A)]) < epsilon
dist3(A,B; epsilon = 1.0) = (&)([abs(A[i] - B[i]) < epsilon for i = 1:length(A)]...)
dist2(A,B; epsilon = 1.0) = sum([abs(A[i] - B[i]) for i = 1:length(A)])

function issquare(x)
  size(x)[1] == size(x)[2]
end

function eigen(A, nsamples::Integer; precision=0.001, epsilon = 0.01)
  @assert issquare(A)
  len = size(A)[1]
  v = mvuniform(0.1,1.0, len)
  # V is nonzero
  λ = uniform(0, 1.0)

  sol = rand((A,v,λ), dist3(A*v, λ*v; epsilon=epsilon), nsamples; parallel=true, precision=precision, RandVarType=Sigma.SymbolicRandVar)
  return sol
end

A = mvuniform(0,1,5,5)

sol = eigen(A, 10; epsilon = 0.0001, precision=0.00001)
A = sol[1][1]
v = sol[2][1]
λ = sol[3][1]
dist2(A*v, λ*v)
