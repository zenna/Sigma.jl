distrname(X::ElementaryRandVar) = string(typeof(X).name)
distrname(X::SymbolicRandVar) = "CompositeRandVar"

function run(X, field::Symbol)
  "$(X.(field))"
end

get_params(X::SymbolicRandVar) = "(ndims=$(ndims(X)))"

function get_params(X::ElementaryRandVar)
  params = ["$field=$(run(X,field))" for field in fieldnames(X)]
  string("(",join(params, ", "),")")
end

show{T}(io::IO, X::SymbolicRandVar{T}) =
  print(io, "$(distrname(X)){$T}$(get_params(X))")

show{T}(io::IO, X::ConstantRandVar{T}) = print(io, X.val)