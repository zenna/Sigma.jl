module Sigma

using Cxx
using IBEX
using Distributions
using AbstractDomains
using Lens
using DataStructures
using Compat

import AbstractDomains: dims, Interval, Boxes
import Distributions: quantile

if VERSION < v"0.4.0-dev"
  using Docile
  # call is in base in 0.4
  export call
  call(f::Function, x) = f(x)
  juliadir = joinpath(homedir(),".julia","v0.3")
else
  import Base: call
  juliadir = joinpath(homedir(),".julia","v0.4")
end

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

import Base: ifelse, cond, isequal, isinf
import Base: sqrt, abs, promote_rule, convert, rand, getindex, string, size
import Base: show, print, showcompact
import Base: sum, dot, length, join, round
import Base: ndims, endof
import Base.isapprox
import Base.start
import Base.next
import Base.done
import Base: hash
import Base: ndims, isequal, union, push!, string, print, show, println
import Base.eltype
import Base.size
import Base.all
import Base: one, zero, norm, similar
import Base: var

import Base:  asin,
              sqrt,
              exp,
              log,
              cos,
              sin,
              tan,
              acos,
              asin,
              atan,
              cosh,
              sinh,
              tanh,
              acosh,
              asinh,
              atanh,
              abs,
              atan2,
              max,
              min,
              sign

# import Lens:benchmark
import Distributions: quantile

export
  # Random Variables
  RandVar,
  RandArray,
  PureRandArray,
  RandVarAI,

  # Abstract Domains
  rangetype,

  LA,
  Lifted,
  liftedarray,
  LiftedArray,

  # Preimages
  pre_recursive,
  pre_greedy,
  pre_deepening,
  prob,
  cond_prob,
  prob_deep,
  cond_prob_deep,
  prob_sampled,
  cond_prob_sampled,
  conditional,

  ndcube,
  sqr,

  # Inference queries
  prob,
  prob_bfs,
  sample_mean,
  cond_prob_mh,
  cond_prob_bfs,
  cond_sample,
  cond_sample_mh,
  cond_sample_bfs,
  setindex,

  # Distributions
  normal,
  uniform,
  flip,
  exponential,
  betarv,
  gamma,
  categorical,
  geometric,
  discreteuniform,
  iid,

  dirichlet,
  mvnormal,
  mvuniform,

  @noexpand,

  #utils
  to_dimacs,
  tolerant_eq,
  rand_select,
  sqr,
  ≊,
  pnormalize,

  #Plotting
  loadvis,
  plot_2d_boxes,
  plot_density,
  plot_cond_density,
  plot_volume_distribution,
  plot_performance,
  plot_sat_distribution,
  distinguished_colors,
  rand_color,
  plot_sample_cond_density,
  plot_sample_density

include("util.jl")
include("domains.jl")
include("omega.jl")
include("sat/sat.jl")
include("sat/cmsat.jl")
include("randvar.jl")
include("refinement.jl")
include("query.jl")
include("distributions.jl")

# Hack to avoid loading Gadfly each time
vispath = joinpath(juliadir, "Sigma","src","vis.jl")

loadvis() = include(vispath)

end
