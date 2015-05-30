## Independent RandVars
## ====================
function iid(T::DataType, c::Function,
             nrows::Int64, ncols::Int64; offset::Int64 = 0)
  a = RandVar{T}[c(i+(j-1)*(nrows) + offset) for i = 1:nrows, j = 1:ncols]
  PureRandArray{T,2}(a)
end

function iid(T::DataType, R::DataType, c::Function, nrows::Int64; offset = 0)
  v::Array{R{T}} = [c(i + offset) for i = 1:nrows]
  PureRandVector{T,R{T}}(v)
end
