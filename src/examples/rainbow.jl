using Sigma

rainy = flip(0.3)
sunny = flip(0.6)
rainbow = @If rainy & sunny flip(0.9) false
prob(rainbow, max_depth = 30)
