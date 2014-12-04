using Sigma

# Constrain a
function issymmetric(x)
  n = length(x)
  middle = div(n,2)+1
  x[1:middle-1] == x[length(x):-1:middle]
end

Xs = iid(Int64, i->discreteuniform(i,1,25), 200)
c = issymmetric(Xs)
cond_sample_mh(Xs,c,1)
