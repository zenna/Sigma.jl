global const SIGMA_SOLVER_ON = true
import Base: call
using Cxx
using IBEX
juliadir = joinpath(homedir(),".julia","v0.4")

## Include (C++) sigma and crpytominisat
cxx_includes = ["/usr/local/include",
                "/home/zenna/repos/sigma"]

for cxx_include in cxx_includes
  addHeaderDir(cxx_include; kind = C_System)
end

cxx"""
  #include <memory>
  #include <cmsat/Solver.h>
  #include "sigma/sigma.h"
"""
@compat Libdl.dlopen("libcryptominisat-2.9.9.so", Libdl.RTLD_LAZY|Libdl.RTLD_DEEPBIND|Libdl.RTLD_GLOBAL)

import dReal:model

# include("sat/sat.jl")
include("sat/cmsat.jl")