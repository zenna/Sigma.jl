using Sigma

## Coin Flipping
## =============

# Suppose you pick up a coin.  How will your belief about how biases it is
# vary when you collect evidence by flipping the coin?
# How does this depend on your prior belief about the coin?
coinweight = betarv(1/2,1/2)
fliprvs = RandVarAI{Bool}[flip(i, coinweight) for i = 1:5]
samples = cond_sample_mh(coinweight, fliprvs[1] & !fliprvs[2], 10, max_iters = 100)
