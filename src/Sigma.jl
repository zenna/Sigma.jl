module Sigma

using Distributions

import Base: ifelse, cond, isequal, isinf
import Base: sqrt, abs, promote_rule, convert, rand, getindex, string, size
import Base: show, print, showcompact
import Base: sum, dot, length, join, round
import Base: call

import Distributions: quantile

export
  RandVar,
  RandomArray,
  MakeRandomArray,
  independentRandomArray,
  Omega,
  SampleOmega,
  Interval,
  NDimBox,
  AbstractBool,
  T, F, TF,
  @If,
  @While,
  rangetype,

  RandArray,
  PureRandArray,
  RandVarSymbolic,

  Lifted,
  liftedarray,

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

  # Probabilistic functions
  prob,
  prob_deep,
  prob_bfs,
  cond_sample,
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

  # Relation
  Var,

  @noexpand,

  #utils
  tolerant_eq,
  rand_select,
  sqr,
  ≊,

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

  # Benchmarking
  parse_output,
  run_church,
  stat_line_layer,
    stat_ribbon_layer,
  stat_errorbar_layer,
  plot_cond_performance,
  plot_prob_performance,
  add_KL!,
  add_KL_church!

include("domains.jl")
include("randvar.jl")
include("common.jl")
include("controlflow.jl")
include("util.jl")
include("omega.jl")
include("refinement.jl")
include("query.jl")
include("distributions.jl")
include("relation.jl")
# include("benchmarks/benchmark.jl")
# include("lazy.jl")

# Hack to avoid loading G= adfly each time
vispath = joinpath(homedir(),".julia","v0.3","Sigma","src","vis.jl")
loadvis() = include(vispath)

end
