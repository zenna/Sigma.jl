module Sigma

using Distributions

import Base: ifelse
import Base: sqrt, abs, promote_rule, convert, rand, getindex, string, size
import Base: show, print, showcompact
import Base: sum, dot, length, join

export
  RandomVariable,
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

  # Preimages
  pre_recursive,
  pre_greedy,
  pre_deepening,
  cond_prob_deep,

  ndcube,
  sqr,

  # Probabilistic functions
  prob,
  prob_deep,
  cond_sample,
  setindex,

  # Distributions
  normal,
  uniform,
  flip,
  uniformArray,

  #utils
  tolerant_eq,
  rand_select,

  #Plotting
  plot_2d_boxes,
  plot_psuedo_density,
  plot_cond_density,
  plot_volume_distribution,
  plot_performance,
  plot_sat_distribution,
  distinguished_colors,
  rand_color,

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
include("randomvariable.jl")
include("controlflow.jl")
include("util.jl")
include("omega.jl")
include("refinement.jl")
include("query.jl")
include("distributions.jl")
# include("benchmarks/benchmark.jl")
# include("lazy.jl")
include("vis.jl")
end
