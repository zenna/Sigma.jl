using Sigma
import Sigma: flipmeta
## From probmods.org / Kahnenman and Tversky
## ==========================================

# The probability of breast cancer is 1% for a woman at 40 who
# participates in a routine screening. If a woman has breast cancer, the probability is
# 80% that she will have a positive mammography. If a woman does not have breast cancer,
# the probability is 9.6% that she will also have a positive mammography.
# A woman in this age group had a positive mammography in a routine screening.
function ground_truth(cancer_rate)
  (cancer_rate * 0.008) / ((0.008 * cancer_rate) + (0.00096 * 0.99))
end

# Model
cancer_base_rate = 0.01
breast_cancer = flip(1,cancer_base_rate)
positive_mammogram = ifelse(breast_cancer,flip(2, 0.8),flip(3,0.096))

# Queries
prob(positive_mammogram)
prob_sampled(positive_mammogram,nsamples = 100000)
cond_prob(breast_cancer, positive_mammogram, box_budget = 1E5, max_iters = 1E5)
cond_prob_sampled(breast_cancer, positive_mammogram)

## SMT version
## ===========
breast_cancer = flipmeta(1,cancer_base_rate)
positive_mammogram = ifelse(breast_cancer,flipmeta(2, 0.8),flipmeta(3,0.096))
prob(positive_mammogram, box_budget = 51)

# Creates 3D preimage plots (for printing with mathematica)
function plot_cancer()
  print(plot_preimage3D(positive_mammogram;box_budget = 200))
  bds = [cond_prob(breast_cancer, positive_mammogram;box_budget = i) for i in [0,1,10,50,200,500]]
  pres =pre_tlmh(positive_mammogram, t, LazyOmega(), 500; frac_in_preimage=1.0)
  plot_preimage3D()
  mhpics = [plot_preimage3D(pres[1:i],Omega{Interval}[]) for i in [1,6,10,50,200,500]]
  print(mhpics[6])
  pics2 = [plot_preimage3D(breast_cancer & positive_mammogram;box_budget = i) for i in [0,1,10,50,200,500]]
  print(pics[5])
  print(pics2[6])
end