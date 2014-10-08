using Sigma

## Coin Flipping
## =============

# Suppose you pick up a coin.  How will your belief about how biases it is
# vary when you collect evidence by flipping the coin?
# How does this depend on your prior belief about the coin?

coinweight = uniform(0, 0.38, 0.6101)
coinweight = normal(0, 0.55, 0.05)
Sigma.plot_sample_density(coinweight, 1000)
plot_density(coinweight, 0.0, 1.0, n_bars = 40)

flips = [flip(i,coinweight) for i=1:3]
cond_prob_deep((coinweight > 0.75) & (coinweight < (0.75 + 0.025)),
                  flips[1] & flips[2] & flips[3] &
                  (coinweight >= 0) & (coinweight <= 1), max_depth = 40)

Sigma.plot_sample_cond_density(coinweight,
                         flips[1] & flips[2] & flips[3],
                         1000000,
                         max_depth = 20)

plot_cond_density(coinweight,
                  flips[1] & flips[2] & flips[3] &
                  (coinweight >= 0) & (coinweight <= 1),
                  0.0, 1.0, n_bars = 40 , max_depth = 40)
