## RandVar Precision
## =================


global DEFAULT_PREC = 0.01 #precision

"""Get default the value of δ.  A higher precision means a more accurate result,
but probably slower solving."""
default_precision() = (global DEFAULT_PREC; DEFAULT_PREC)

"""Set default the value of δ.  For many inference queries `precision=...`
can be passed directly instead.  A higher precision means a more accurate result,
but probably slower solving."""
function set_default_precision!(x::Float64)
  println("Setting default precision to $x")
  global DEFAULT_PREC
  DEFAULT_PREC = x
end
