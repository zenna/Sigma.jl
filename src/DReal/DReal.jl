module DReal

using AbstractDomains
using Compat
using MathProgBase

@windows_only error("Windows not supported")

# @show joinpath(dirname(@__FILE__),"..","deps","deps.jl")
# if isfile(joinpath(dirname(@__FILE__),"..","deps","deps.jl"))
#     include("../deps/deps.jl")
# else
#     error("DReal not properly installed. Please run Pkg.build(\"DReal\")")
# end

VERSION < v"0.4-" && using Docile

deps_dir = joinpath(joinpath(Pkg.dir("Sigma"),"deps"))
prefix = joinpath(deps_dir,"usr")
src_dir = joinpath(prefix,"src")
bin_dir = joinpath(prefix,"bin")
lib_dir = joinpath(prefix,"lib")

try
  @osx? begin
    @compat Libdl.dlopen(joinpath(lib_dir, "libdreal.dylib"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
  end : begin
    @compat Libdl.dlopen(joinpath(lib_dir, "libprim.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
    @compat Libdl.dlopen(joinpath(lib_dir, "libCoinUtils.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
    @compat Libdl.dlopen(joinpath(lib_dir, "libClp.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
    @compat Libdl.dlopen(joinpath(lib_dir, "libcapd.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
    @compat Libdl.dlopen(joinpath(lib_dir, "libibex.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
    @compat Libdl.dlopen(joinpath(lib_dir, "libdreal.so"), Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)
  end
catch e
  println("Could not load required shared libraries")
  rethrow(e)
end

import Base: print, show
import Base:  abs, exp, log,
              ^, sin, cos,
              tan, asin, acos,
              atan, sinh, cosh,
              tanh, atan2, sqrt

import Base: ifelse
import Base: convert, push!
import Base: ==, >=, <=, >, <, /, -, +, *, &, |, !

export
  Context,
  Logic,
  model,
  init_dreal!,
  set_precision!,
  init_dreal!,
  Var,
  ForallVar,
  Ex,
  add!,
  is_satisfiable,
  global_context,
  set_verbosity_level!,
  push_ctx!,
  pop_ctx!,
  reset_ctx!,
  delete_ctx!,
  reset_global_ctx!,
  →,
  implies,
  minimize,
  default_global_context

## Global defaults
const DEFAULT_PRECISION = 0.001

include("wrap_capi.jl")
include("logic.jl")
include("context.jl")
include("environment.jl")
include("expression.jl")
include("construct.jl")
include("optimize.jl")
include("ode.jl")
include("SolverInterface.jl")
include("util.jl")

export
  qf_uf,         # Uninterpreted Functions
  qf_nra,        # Non-Linear Real Arithmetic
  qf_nra_ode,    # Non-Linear Real Arithmetic
  qf_bv,         # BitVectors
  qf_rdl,        # Real difference logics
  qf_idl,        # Integer difference logics
  qf_lra,        # Real linear arithmetic
  qf_lia,        # Integer linear arithmetic
  qf_ufidl,      # UF + IDL
  qf_uflra,      # UF + LRA
  qf_bool,       # Only booleans
  qf_ct          # Cost

init_dreal!()
create_global_ctx!()

end
