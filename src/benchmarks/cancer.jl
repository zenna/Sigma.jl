using Sigma

function ground_truth(cancer_rate)
  (cancer_rate * 0.008) / ((0.008 * cancer_rate) + (0.00096 * 0.99))
end

ptrue_to_dist(ptrue::Float64) = [1 => ptrue, 0 => (1 - ptrue)]

groundtruthcancer = ground_truth(0.01)
ground_truth_dist = ptrue_to_dist(ground_truth(0.01))

KL(ptrue_to_dist(ground_truth(0.01)),ptrue_to_dist(.9))
breast_cancer = flip(1,0.01)
positive_mammogram = @If breast_cancer flip(2, 0.8) flip(3,0.096)
cond_prob_deep(breast_cancer, positive_mammogram,$$ max_depth = 10)
prob_deep(positive_mammogram)
sampler = cond_sample(breast_cancer, positive_mammogram,max_depth = 12)

num_true = 0
@time for i = 1:1000
  s = sampler(100)
  if s
    num_true += 1
  end
end
num_true/1000

cond_prob_deep(breast_cancer, positive_mammogram, max_depth = 12)
cond_prob_deep(breast_cancer, positive_mammogram, max_depth = 8)
sigma_stats = plot_cond_performance(breast_cancer, positive_mammogram, num_points = 10)
add_KL!(sigma_stats, ptrue_to_dist(ground_truth(0.01)))
sigma_layer = stat_errorbar_layer(sigma_stats[2:],"run_time","klmin","klmax")

multi_sigma_stats =
  [plot_cond_performance(breast_cancer, positive_mammogram, num_points = 2, max_depth = i)
   for i = 1:10]

[add_KL!(s,ground_truth_dist) for s in multi_sigma_stats]
multi_sigma_layers = map(s->stat_errorbar_layer(s,"run_time","klmin","klmax"),multi_sigma_stats)

church_stats = run_church("rej.church")
add_KL_church!(church_stats,ground_truth_dist)
church_layer = stat_line_layer(church_stats,"run_time","kl")
plot(multi_sigma_layers[5],church_layer)
