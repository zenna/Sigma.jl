using Sigma

A = gamma(2,3)
plot_sample_cond_density(A,abs(A-round(A)) < 1E-5,100000, max_depth = 50)
