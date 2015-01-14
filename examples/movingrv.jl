using Sigma
Sigma.loadvis()

# Process
function moving_normal(nsteps::Int64)
  Xs = PureRandArray(Float64, nsteps)
  Xs[1] = normal(0,0.,3.)
#   for i = 1:nsteps - 1
#     Xs[i+1] = Xs[i] + 3.
#   end

  for i = 1:nsteps - 1
    Xs[i+1] = ifelse(Xs[i]< 10., Xs[i] + 2., Xs[i])
  end
  Xs
end

X = moving_normal(10)

plot_sample_cond_density(X[1], (X[3] > 5.0) & (X[3] < 6.0), 2000)

plot_sample_density(X[10], 2000)

plot_psuedo_density(X, 0.,20.,n_bars = 100)
cond_prob(X[8] > 8., X[2] < 2.0)
