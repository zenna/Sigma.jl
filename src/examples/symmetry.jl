using Sigma

# Gererates a symmetric vector of integers
# function issymmetric2(Xs::LiftedArray{Int64,1})
#   n = length(Xs)
#   condition = true
#   if n > 1 # always symmetric when length == 1
#     starti = iseven(n) ? n/2+1 : (n+1)/2 + 1
#     j = 1
#     for i = length(Xs):-1:int(starti)
#       condition = condition & (Xs[j] ≊ Xs[i])
#       j += 1
#     end
#   end
#   condition
# end

function issymmetric(x)
  n = length(x)
  middle = div(n,2)+1
  x[1:middle-1] == x[length(x):-1:middle]
end

Xs = iid(Int64, i->discreteuniform(i,1,26), 40)
c = issymmetric(Xs)
cond_sample_mh(Xs,c,1)
