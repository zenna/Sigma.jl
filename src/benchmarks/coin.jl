using Sigma

function tosatboxes(pre)
  sat =  Sigma.sat_tree_data(pre)
  map(x->convert(Sigma.NDimBox,collect(values(x.intervals))),sat)
end

function tomixedboxes(pre)
  mixed =  Sigma.mixedsat_tree_data(pre)
  map(x->convert(Sigma.NDimBox,collect(values(x.intervals))),mixed)
end

# Coin Weight
coinweight = uniform(0, 0.38, 0.6101)
flips = [flip(i,coinweight) for i=1:3]
cond_prob_deep((coinweight > 0.75) & (coinweight < (0.75 + 0.025)),
                  flips[1] & flips[2] & flips[3] &
                  (coinweight >= 0) & (coinweight <= 1), max_depth = 40)

plot_sample_cond_density(coinweight,
                         flips[1] & flips[2] & flips[3],
                         1000000,
                         max_depth = 20)

plot_cond_density(coinweight,
                  flips[1] & flips[2] & flips[3] &
                  (coinweight >= 0) & (coinweight <= 1),
                  0.0, 1.0, n_bars = 40 , max_depth = 40)
