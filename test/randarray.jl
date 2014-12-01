using Sigma
using Base.Test

Xs = iid(Float64, random, 3,3)
@test 0 <= rand(Xs[1,1]) <= 1
@test 0 <= sum(rand(Xs)) <= 9

As = iid(Float64, random, 3,1)
Bs = iid(Float64, random, 3,1)

Qs = iid(Float64, i->normal(i,0.,1.),4)
call(Qs,Omega())

## Benchmarking
Xs = iid(Float64,i->uniform(i,0,2),40)
S = sum(Xs)
Y = (S > 3) & (S < 4)
samples = cond_sample_mh(Xs,Y,2)



times = Float64[]
for i = 1:20
  Xs = iid(Float64,i->uniform(i,0,2),i)
  S = sum(Xs)
  Y = (S > 3) & (S < 4)
  tic()
  samples = cond_sample_mh(Xs,Y, 20, max_iters = 10)
  t = toc()
  push!(times, t)
  @show sum(samples[1])
end
