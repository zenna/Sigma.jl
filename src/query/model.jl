## Model
## =====

"""Generates a 'model' from X given that Y is true, a model is like a model
  except that it does not follow any well defined distribution"""
function abstract_model(Y::DRealRandVar{Bool})
  DReal.push_ctx!(Y.ctx)

  # Since we are not interested in correct distribution we will consider
  # the entire sample space - i.e. unit hypercube.
  A = Sigma.LazyOmega(Float64)
  for (symb, var) in Y.sym_to_var
    interval = bounds(symb, A)
    add_bound_constraints!(Y.ctx, var, interval.l, interval. u)
  end

  DReal.add!(Y.ctx, Y.ex)
  !is_satisfiable(Y.ctx) && "Cannot draw model from unsatisfiable condition"

  # Let's extract the model
  preimage_model = LazyBox(Float64)
  for (symb, var) in Y.sym_to_var
    @show symb
    if isa(symb, OmegaRandVar)
      @show symb.dim
      preimage_model[symb.dim] = model(Y.ctx,var.ex)
    end
  end

  DReal.pop_ctx!(Y.ctx)
  preimage_model
end

"`n` conditional models from `X` given `Y` is true"
function abstract_cond_model{T}(X::ExecutableRandVar{T},
                                Y::RandVar{Bool})
  RT = rangetype(X)
  abstract_preimage_model = abstract_model(Y)
  X(preimage_model)
end

"`n` conditional models from `X` given `Y` is true"
function cond_model{T}(X::ExecutableRandVar{T},
                       Y::RandVar{Bool})
  RT = rangetype(X)
  abstract_preimage_model = abstract_model(Y)
  preimage_model = mid(abstract_preimage_model)
  X(preimage_model)
end

## Convenience
## ===========

"Construct a value from for 'X' given that predicate 'Y' is true"
function model{T}(X::SymbolicRandVar{T},
                  Y::SymbolicRandVar{Bool};
                  RandVarType = default_randvar())
  # FIXME: Problem here is that dreal will find constraints e.g. in terms
  # of bounds on a normal distribution, but to get an abstract preimage sample
  # we want them in terms of Omega. Either we need to go backwards from normal
  # interval to preimage interval, or adapt the calling of random variables with
  # normal interval values.
  warn("Model will not work with non-closed form random variables")
  executable_X = convert(ExecutableRandVar{T}, X)
  executable_Y = convert(RandVarType{Bool}, Y)
  cond_model(executable_X, executable_Y)
end
