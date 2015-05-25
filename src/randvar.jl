@doc "Random Variables are functions from the sample space to some other space" ->
abstract RandVar{T}

@doc "The type of the range of a random variable" ->
rangetype{T}(X::RandVar{T}) = T

@doc "Return a Set of dimension indices of a random variable" ->
function dims(X::RandVar)
  # Do a depth first search and find union of dimensions of all OmegaRandVars
  dimensions = Set{Int}()
  visited = Set{RandVar}()
  tovisit = Set{RandVar}([X])
  while !isempty(tovisit)
    v = pop!(tovisit)
    if isa(v,OmegaRandVar)
      push!(dimensions, dims(v)...)
    else
      for arg in args(v)
        arg ∉ visited && push!(tovisit,arg)
      end
    end
  end
  dimensions
end

@doc "Number of dimensions of a random variable" ->
ndims(X::RandVar) = length(dims(X))

function isequal(X::RandVar,Y::RandVar)
  # Equivalent Random variables should (at least) have same type and #args
  typeof(X) != typeof(Y) && (return false)
  x_args = args(X)
  y_args = args(Y)
  length(x_args) != length(y_args) && (return false)
  for i = 1:length(x_args)
    !isequal(x_args[i],y_args[i]) && (return false)
  end
  true
end

pipeomega(v, ω) = v
pipeomega(v::RandVar, ω) = call(v,ω)

rand(X::RandVar) = call(X,LazyRandomVector(Float64))
rand{T}(X::RandVar{T},nsamples::Int) = T[call(X,LazyRandomVector(Float64)) for i= 1:nsamples]

# default aliases
rand(X::RandVar,Y::RandVar{Bool};pre_args...) = cond_sample_bfs(X,Y;pre_args...)
rand(X::RandVar,Y::RandVar{Bool},nsamples::Int;pre_args...) = cond_sample_bfs(X,Y,nsamples;pre_args...)

for finame in ["randvarsuper.jl"]
    include(joinpath("randvar", finame))
end

## Convenience synonym
# RandArray = PureRandArray
