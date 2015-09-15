using Sigma
using Lens
## Non-Negative Matrix Factorization

Sigma.restart_counter!()

dist(A,B; epsilon = 1.0) = sum([abs(A[i] - B[i]) for i = 1:length(A)]) < epsilon
dist3(A,B; epsilon = 1.0) = (&)([abs(A[i] - B[i]) < epsilon for i = 1:length(A)]...)
dist2(A,B; epsilon = 1.0) = sum([abs(A[i] - B[i]) for i = 1:length(A)])

function nmf(V, W, H; epsilon = 1.0)
  dist3(V, W*H; epsilon = epsilon)
end

function benchmark_nmf(m::Integer, k::Integer, n::Integer, nsamples::Integer,
                      epsilon::Float64, precision::Float64)
  Sigma.restart_counter!()
  srand(1234)
  W = Sigma.mvuniform(0.0,1.0,m,k)
  H = Sigma.mvuniform(0.0,1.0,k,n)

  # Generate date
  W_data = rand(m,2)
  H_data = rand(2,n)
  V = W_data*H_data
  # sol = Sigma.point_sample_mc(nmf(V, W, H; epsilon=0.05), nsamples, parallel = true, precision=0.001)
  #
  sol = rand((W,H), nmf(V, W, H; epsilon=epsilon), nsamples; parallel=true, precision=precision, RandVarType=Sigma.SymbolicRandVar)
  for i = 1:length(sol[1])
    W_conc = sol[1][i]
    H_conc = sol[2][i]
    prodWH = W_conc * H_conc
    lens(:distance, dist2(V,prodWH))
  end
  return sol, V
end

# function benchmark_nmf_rj(m::Integer, k::Integer, n::Integer, nsamples::Integer,
#                       epsilon::Float64, precision::Float64)
#   Sigma.restart_counter!()
#   srand(1234)
#   W = Sigma.mvuniform(0.0,1.0,m,k)
#   H = Sigma.mvuniform(0.0,1.0,k,n)
#
#   # Generate date
#   W_data = rand(m,2)
#   H_data = rand(2,n)
#   V = W_data*H_data
#   # sol = Sigma.point_sample_mc(nmf(V, W, H; epsilon=0.05), nsamples, parallel = true, precision=0.001)
#   #
#   nmf(V, W, H; epsilon=epsilon)
# end

function sample_variance{T,N}(samples::Vector{Array{T,N}})
  centerofmass::Array = mean(samples)
  distances = [sqrt(sum((sample - centerofmass).^2)) for sample in samples]
  sum(distances) / (length(samples) - 1)
end

results, stats = capture(()->benchmark_nmf(3,2,3,100,0.01,0.001), [:distance, :sat_check, :post_loop])

timediffs = vcat(get(stats, proc_id=1, lensname=:sat_check), get(stats, proc_id=1, lensname=:sat_check))
timediffs = vcat(get(stats, proc_id=1, lensname=:sat_check), get(stats, proc_id=2, lensname=:sat_check))

timediffs = map(i->float(i)/1e9, timediffs)
