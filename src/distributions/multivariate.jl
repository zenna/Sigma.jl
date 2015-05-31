function mvuniform(offset::Integer, lb::Real, ub::Real, nrows::Integer, ncols::Integer)
    iid(Float64, i->uniform(i, lb,ub), nrows, ncols, offset = offset)
end

mvuniform(lb::Real, ub::Real, n::Integer) = PureRandArray(RandVar{Float64}[uniform(lb,ub) for i = 1:n])

## Independent RandVars
## ====================
function iid(T::DataType, c::Function,
             nrows::Int64, ncols::Int64; offset::Int64 = 0)
  a = RandVar{T}[c(i+(j-1)*(nrows) + offset) for i = 1:nrows, j = 1:ncols]
  PureRandArray{T,2}(a)
end

function iid(T::DataType, c::Function, nrows::Int64; offset = 0)
  a = RandVar{T}[c(i + offset) for i = 1:nrows]
  PureRandArray{T,1}(a)
end
