using Sigma
using Base.Test

# Constrain an array of integers to be symmetric
function issymmetric(x)
  n = length(x)
  middle = div(n,2)+1
  x[1:middle-1] == x[length(x):-1:middle]
end

Xs = mvuniform(0,25,100)
sample = rand(Xs, issymmetric(Xs))
