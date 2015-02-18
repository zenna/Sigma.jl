# When condition is TF we need to evaluate both branches
# and merge with ⊔
function ifelse(c::AbstractBool, x, y)
  if c === T
    x
  elseif c === F
    y
  elseif c === TF
    ⊔(x,y)
  end
end