
module Sigma

using DReal

using Distributions
using AbstractDomains
using Lens
using DataStructures
using Compat

import Base: ifelse, cond, isequal, isinf
import Base: sqrt, abs, promote_rule, convert, rand, getindex, string, size
import Base: show, print, showcompact
import Base: sum, dot, length, join, round
import Base: ndims, endof
import Base.isapprox
import Base: start, next, done
import Base: hash
import Base: ndims, isequal, union, push!, string, print, show, println
import Base.eltype
import Base.size
import Base.all
import Base: one, zero, norm, similar
import Base: real
import Base: var
import Base: in

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

import AbstractDomains: dims, Interval, Boxes
import Distributions: quantile

# Solvers
global const DREAL_SOLVER_ON = true
global const DREAL_BINARY_SOLVER_ON = true

if VERSION < v"0.4.0-dev"
  include("Sigma1.jl")
else
  include("Sigma2.jl")
end

## Global Cosntants
const DEFAULT_PREC = 0.0001 #precision

export
  # Random Variables
  RandVar,
  RandArray,
  RandArray,
  RandVarAI,
  dims,


  # Abstract Domains
  rangetype,

  LA,
  Lifted,
  liftedarray,
  LiftedArray,

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
  model,

  # RandVar Types
  RandVar,
  AllRandVars,

  # Distributions
  normal,
  uniform,
  flip,
  exponential,
  logistic,
  betarv,
  gamma,
  categorical,
  geometric,
  discreteuniform,
  iid,

  dirichlet,
  mvnormal,
  mvuniform,
  mvexponential,
  mvlogistic,

  @noexpand,

  #utils
  to_dimacs,
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
  plot_sample_density,

  #Solver
  DRealSolver,

  # RandVars
  DRealRandVar,
  DRealBinaryRandVar

include("util.jl")
include("domains.jl")
include("omega.jl")
include("randvar.jl")
include("solver.jl")
include("refinement.jl")
include("query.jl")
include("distributions.jl")
include("split.jl")
include("pmaplm.jl")

# Hack to avoid loading Gadfly each time
vispath = joinpath(juliadir, "Sigma","src","vis.jl")

loadvis() = include(vispath)

end
