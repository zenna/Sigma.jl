using Sigma

# Models a particle moving in 1 dimensional space where
# position is subject to uncertainty
function moving_normal(nsteps::Int64)
  Xs = PureRandArray(Float64, nsteps)
  Xs[1] = normal(0,0.,3.)
  for i = 1:nsteps - 1
    Xs[i+1] = ifelse(Xs[i]< 10., Xs[i] + 2., Xs[i])
  end
  Xs
end

X = moving_normal(10)
cond_prob(X[8] > 8., X[2] < 2.0)