module Sigma

using Distributions
using AbstractDomains
using Lens
using DataStructures
using Compat

# SMT Solvers
using dReal

import AbstractDomains: dims

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
  random,
  normal,
  uniform,
  flip,
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

include("common.jl")
include("util.jl")
include("pmaplm.jl")
include("joins.jl")
include("domains.jl")
include("omega.jl")
include("smtsolver.jl")
include("randvar.jl")
include("lift.jl")
include("refinement.jl")
include("query.jl")
# include("distributions.jl")

# Hack to avoid loading Gadfly each time
vispath = joinpath(juliadir, "Sigma","src","vis.jl")

loadvis() = include(vispath)

end
