using Base.Test

box = Sigma.unit_box(AbstractDomains.LazyBox{Float64}, Set([1,2,3]))
@test dims(box) == 3