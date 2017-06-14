distrname(X::ElementaryRandVar) = string(typeof(X).name)
distrname(X::SymbolicRandVar) = "CompositeRandVar"

"For SymbolcRandVar just retrn ndims"
get_params(X::SymbolicRandVar) = "(ndims=$(ndims(X)))"

"Parameters in form p1=value, e.g. (dim=1, lb=0.0, ub=1.0)"
function get_params(X::ElementaryRandVar)
  params = ["$field=$(getfield(X,field))" for field in fieldnames(X)]
  string("(",join(params, ", "),")")
end

"Show a RandVar with its parameters e.g.,(dim=1, lb=0.0, ub=1.0)"
function show{T}(io::IO, X::SymbolicRandVar{T})
  print(io, "$(distrname(X)){$T}$(get_params(X))")
end

show{T}(io::IO, X::ConstantRandVar{T}) = print(io, X.val)
