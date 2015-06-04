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

@doc "Apply a random variable to some randomness" ->
call(X::RandVar,ω::Omega) = lambda(X)(ω)

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

for finame in ["types.jl",
               "compile.jl",
               "randarray.jl"]
    include(joinpath("randvar", finame))
end
  

# All Random Variables
typealias AllRandVars Union(RandVar, PureRandArray)
typealias Lift{T} Union(T,RandVar{T})

@compat in{T}(X::RandVar, bounds::Tuple{Lift{T},Lift{T}}) = (X >= bounds[1]) & (X <=  bounds[2])

## Printing
## ========
function to_dimacs(Y::Sigma.RandVar{Bool})
  cmap, cnf, ω, aux_vars = Sigma.analyze(Y)
  indep_vars = join(values(cmap), " ")
  last_var = var(cnf[length(cnf)][1])
  println("cnf $last_var $(length(cnf))")
  println(string(cnf))
  println("c ind $indep_vars")
end
