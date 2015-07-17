function mvuniform(offset::Integer, lb::Real, ub::Real, nrows::Integer, ncols::Integer)
    iid(Float64, i->uniform(i, lb,ub), nrows, ncols, offset = offset)
end

"Multivariate Uniform Vector"
mvuniform(lb::Real, ub::Real, n::Integer) = RandArray(RandVar{Float64}[uniform(lb,ub) for i = 1:n])
"Multivariate Uniform Matrix"
mvuniform(lb::Real, ub::Real, nrows::Integer, ncols::Integer) =
  RandArray(RandVar{Float64}[uniform(lb,ub) for i = 1:nrows,j=1:ncols])

"Multivariate Logistic Vector"
mvlogistic(μ, s, n::Integer) = RandArray(RandVar{Float64}[logistic(μ, s) for i = 1:n])
"Multivariate Logistic Matrix"
mvlogistic(μ, s, nrows::Integer, ncols::Integer) =
  RandArray(RandVar{Float64}[logistic(μ, s) for i = 1:nrows,j=1:ncols])

"Multivariate Exponential Vector"
mvexponential(λ, n::Integer) = RandArray(RandVar{Float64}[exponential(λ) for i = 1:n])

"Multivariate Exponential Matrix"
mvexponential(λ, nrows::Integer, ncols::Integer) =
  RandArray(RandVar{Float64}[exponential(λ) for i = 1:nrows,j=1:ncols])

"Multivariate Normal Vector"
mvnormal(μ, σ, nrows::Integer) =
  RandArray(RandVar{Float64}[normal(μ, σ) for i = 1:nrows])

"Multivariate Normal Matrix"
mvnormal(μ, σ, nrows::Integer, ncols::Integer) =
  RandArray(RandVar{Float64}[normal(μ, σ) for i = 1:nrows, j=1:ncols])




## Independent RandVars
## ====================
function iid(T::DataType, c::Function,
             nrows::Int64, ncols::Int64; offset::Int64 = 0)
  a = RandVar{T}[c(i+(j-1)*(nrows) + offset) for i = 1:nrows, j = 1:ncols]
  RandArray{T,2}(a)
end

function iid(T::DataType, c::Function, nrows::Int64; offset = 0)
  a = RandVar{T}[c(i + offset) for i = 1:nrows]
  RandArray{T,1}(a)
end
