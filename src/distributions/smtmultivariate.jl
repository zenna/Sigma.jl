## SMT based Multivariate Distributions
## ====================================

mvuniformsmt(a,b, i::Int, j::Int) = iidsmt(Float64, c->uniformsmt(a,b),i,j)
mvuniformsmt(a,b, i::Int) = iidsmt(Float64, c->uniformsmt(a,b),i)

mvnormalsmt(μ,σ, i::Int, j::Int) = iidsmt(Float64, c->normalsmt(μ,σ),i,j)
mvnormalsmt(μ,σ, i::Int) = iidsmt(Float64, c->normalsmt(μ,σ),i)
