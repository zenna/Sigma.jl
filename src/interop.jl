## Interoperability with Distributions.jl random variables
## ========================================================

## Conversion between Sigma random variaables and Distribution.jl random variables
## ===============================================================================
# Generates conversion functions of form:
# convert(::Type{Distributions.Poisson}, X::PoissonRandVar) =
#   Distributions.Poisson(X.λ.val)

# get_params(X::ElementaryRandVar, param_names) = [X.(p).val for p in param_names]

# # Generate functions
# for erv_type in subtypes(ElementaryRandVar)
#   # param 1 is dimension, ignore
#   param_names = erv_type.names[2:end]
#   dist_name = interop_name(erv_type)

#   p = Expr(:., :Distributions, QuoteNode(dist_name))
#   eval(:(convert(::Type{Distributions.$dist_name}, X::$(erv_type.name.name)) = $p(get_params(X, $param_names)...)))
# end

concretize(args::Tuple{Vararg{ConstantRandVar}}) = [arg.val for arg in args]
convert{T <: Distributions.Distribution}(D::Type{T}, X::ElementaryRandVar) =
  T(concretize(args(X))...)

interop_name{T <: ElementaryRandVar}(t::Type{T}) = Symbol(string(t.name.name)[1:end-7])
distribution_type{T <: ElementaryRandVar}(t::Type{T}) = getfield(Distributions, interop_name(T))

## Elementary Random Variables with Constant Parameters should be compatible
## with all of Distributios.jl fnuctions
## =========================================================================

## Distributions.jl interface
import Distributions: params, succprob, failprob, scale, location, shape,
  rate, ncategories, ntrials, dof

import Distributions: mean, var, std, median, modes, mode, skewness,
  kurtosis, isplatykurtic, isleptokurtic, ismesokurtic, entropy, entropy,
  mgf, cf

# Probability Evaluation
import Distributions: insupport, pdf, logpdf, loglikelihood, logcdf, ccdf, logccdf,
  cquantile, invlogcdf, invlogccdf

params(X::ElementaryRandVar) = params(convert(Distributions.Distribution, X))
succprob(X::ElementaryRandVar) = succprob(convert(Distributions.Distribution, X))
failprob(X::ElementaryRandVar) = failprob(convert(Distributions.Distribution, X))
scale(X::ElementaryRandVar) = scale(convert(Distributions.Distribution, X))
location(X::ElementaryRandVar) = location(convert(Distributions.Distribution, X))
shape(X::ElementaryRandVar) = shape(convert(Distributions.Distribution, X))
rate(X::ElementaryRandVar) = rate(convert(Distributions.Distribution, X))
ncategories(X::ElementaryRandVar) = ncategories(convert(Distributions.Distribution, X))
ntrials(X::ElementaryRandVar) = ntrials(convert(Distributions.Distribution, X))
