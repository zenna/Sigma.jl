using Base.Test

p = Sigma.pre_partition_bfs(A>0.76, Sigma.LazyOmega(Float64))
p.under
