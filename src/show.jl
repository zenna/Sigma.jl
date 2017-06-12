distrname(X::ElementaryRandVar) = string(typeof(X).name)
distrname(X::SymbolicRandVar) = "CompositeRandVar"

"For SymbolcRandVar just retrn ndims"
get_params(X::SymbolicRandVar) = "(ndims=$(ndims(X)))"

function get_params(X::ElementaryRandVar)
  "Parameters in form p1=value, e.g. (dim=1, lb=0.0, ub=1.0)"
  params = ["$field=$(getfield(X,field))" for field in fieldnames(X)]
  string("(",join(params, ", "),")")
end

function show{T}(io::IO, X::SymbolicRandVar{T})
  "Show a RandVar with its parameters e.g.,(dim=1, lb=0.0, ub=1.0)"
  print(io, "$(distrname(X)){$T}$(get_params(X))")
end

show{T}(io::IO, X::ConstantRandVar{T}) = print(io, X.val)
