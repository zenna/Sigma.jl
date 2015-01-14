using Sigma
Sigma.loadvis()
## From probmods.org / Kahnenman and Tversky
## ==========================================

# The probability of breast cancer is 1% for a woman at 40 who
# participates in a routine screening. If a woman has breast cancer, the probability is
# 80% that she will have a positive mammography. If a woman does not have breast cancer,
# the probability is 9.6% that she will also have a positive mammography.
# A woman in this age group had a positive mammography in a routine screening.

# What is the probability that she actually has breast cancer?

# Ground truth
function ground_truth(cancer_rate)
  (cancer_rate * 0.008) / ((0.008 * cancer_rate) + (0.00096 * 0.99))
end

# Model
breast_cancer = flip(1,0.01)
positive_mammogram = @If breast_cancer flip(2, 0.8) flip(3,0.096)

# Queries
prob(positive_mammogram)
cond_prob(breast_cancer, positive_mammogram, max_depth = 10)
cond_prob_sampled(breast_cancer, positive_mammogram)

## CANCER WITH BETA ELABORATION
## =======================
function ground_truth(cancer_rate)
  (cancer_rate * 0.008) / ((0.008 * cancer_rate) + (0.00096 * 0.99))
end

# Model
cancer_base_rate = betarv(0,0.5,1.0)
plot_sample_histogram(cancer_base_rate,10000)
breast_cancer = flip(1,cancer_base_rate)
positive_mammogram = ifelse(breast_cancer,flip(2, 0.8),flip(3,0.096))

# Queries
prob(positive_mammogram)
prob_sampled(positive_mammogram,nsamples = 100000)
cond_prob(breast_cancer, positive_mammogram, box_budget = 1E5, max_iters = 1E5)
cond_prob_sampled(breast_cancer, positive_mammogram)
