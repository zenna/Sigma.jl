using Base.Test
using Sigma
import Sigma: HyperBox, measure, logmeasure
import Sigma: partial_split_box, mid_split

# What should a domain be
b = HyperBox([0.0 0.0
              2.0 1.0])

@test ndims(b) == 2
@test measure(b) == 2
@test logmeasure(b) == log(2) + 0
@test length(mid_split(b)) == 4
@test length(partial_split_box(b, [1=>0.3])) == 2
