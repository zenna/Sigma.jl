## Model
## =====

@doc """Generates a 'model' from X given that Y is true, a model is like a sample
  except that it does not follow any wel ldefined distribution""" ->
function preimage_model(Y::DRealRandVar{Bool})
  dreal_model = DReal.model(Y)
  !is_satisfiable(Y.ctx) && "Cannot draw model from unsatisfiable condition"
  preimage_sample = LazyBox(Float64)
  for (dim,var) in Y.dimToVar
    preimage_sample[dim] = model(Y.ctx,var)
  end
  preimage_sample
end

function model2(X::AllRandVars, Y::DRealRandVar{Bool})
  push_ctx!(Y.ctx)
  DReal.add!(Y.ctx,Y.ex)
  # println("Checking Satisfiability")
  issat = is_satisfiable(Y.ctx)
  if !issat
    pop_ctx!(Y.ctx)
    error("Cannot draw model from unsatisfiable condition")
  end
  # println("model_is_satisfiable")
  preimage_sample = LazyBox(Float64)
  for (dim,var) in Y.dimtovar
    preimage_sample[dim] = DReal.model(Y.ctx,var)
  end
  pop_ctx!(Y.ctx)
  call(X,rand(preimage_sample))
end

@doc """Generates a 'model' from X given that Y is true, a model is like a sample
  except that it does not follow any well defined distribution""" ->
function model(X::AllRandVars, Y::RandVar{Bool})
  Ydreal = convert(DRealRandVar{Bool}, Y)
  model2(X,Ydreal)
end
