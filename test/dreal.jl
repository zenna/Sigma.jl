using Sigma
using AbstractDomains

a = flip(1)
omegatron = Sigma.abstract_omega(1)
omegatron = HyperBox([Interval(0.501,.51)])
b = convert(Sigma.DRealRandVar{Bool},a)
@show call(b,omegatron)
