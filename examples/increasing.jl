using Sigma
using Base.Test

# Constrain a list to integers to be increasing
function isincreasing(x)
  condition = true
  for i = 1:length(x)-1
    condition &= x[i] < x[i+1]
  end
  condition
end

Xs = iid(Int64, i->discreteuniform(i,1,100), 10)
c = isincreasing(Xs)
xs = cond_sample_mh(Xs,c,1)
@test isincreasing(xs)