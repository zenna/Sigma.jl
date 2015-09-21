
module Sigma

using DReal
using Docile

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
import Base: collect

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

import AbstractDomains: dims, Interval, Boxes
import Distributions: quantile
import DReal: model, set_precision!

if VERSION < v"0.4.0-dev"
  call(f::Function, x) = f(x)
  juliadir = joinpath(homedir(),".julia","v0.3")

  include("Sigmajl3.jl")
else
  include("Sigmajl4.jl")
end

export
  # Random Variables
  RandVar,
  RandArray,
  dims,

  # Abstract Domains
  rangetype,

  LA,
  Lifted,
  liftedarray,
  LiftedArray,

  # Inference queries
  prob,
  sample_mean,

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

  # RandVars
  DRealRandVar,

  # From abstract domains
  mid,

  isapprox,
  quantile

include("util.jl")
include("domains.jl")
include("omega.jl")
include("precision.jl")
include("randvar.jl")
include("interop.jl")
include("refinement.jl")
include("query.jl")
include("distributions.jl")
include("split.jl")
include("pmaplm.jl")
include("show.jl")

# Hack to avoid loading Gadfly each time
vispath = joinpath(juliadir, "Sigma","src","vis.jl")

loadvis() = include(vispath)

end
