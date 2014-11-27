using Base.Test
using Sigma
import Sigma: HyperBox, measure, logmeasure, mid_split

# What should a domain be
b = HyperBox([0.0 0.0
              1.0 1.0])

@test ndims(b) == 2
@test measure(b) == 1.0
@test logmeasure(b) == 0.0
@test length(mid_split(b)) == 4
