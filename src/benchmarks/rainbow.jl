using Sigma

function see_rainbow(scale)
  rainy = flip(0,0.3 * scale)
  sunny = flip(1,0.6 * scale)
  rainbow = @If rainy & sunny flip(2, 0.9 * scale) false
  prob_deep(rainbow, max_depth = 30)
end