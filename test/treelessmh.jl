using Sigma

@show nprocs()
X = Sigma.uniformsmt(0,0,1)
@time Sigma.pre_tlmh(X>0.5, T,Omega())