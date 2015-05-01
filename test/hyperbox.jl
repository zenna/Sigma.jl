using Base.Test
using Sigma
import Sigma: measure, logmeasure

# What should a domain be
b = HyperBox([0.0 0.0
              2.0 1.0])
@test ndims(b) == 2
@test measure(b) == 2
@test logmeasure(b) == log(2) + 0