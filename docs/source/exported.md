# Sigma

## Exported

---

<a id="method__call.1" class="lexicon_definition"></a>
#### call(X::SymbolicRandVar{T}, ω) [¶](#method__call.1)
Apply a random variable to some randomness

*source:*
[Sigma/src/randvar/symbolic.jl:23](file:///home/zenna/.julia/v0.3/Sigma/src/randvar/symbolic.jl)

---

<a id="method__cond_sample.1" class="lexicon_definition"></a>
#### cond_sample{T}(X::ExecutableRandVar{T}, Y::RandVar{Bool}, n::Integer) [¶](#method__cond_sample.1)
`n` conditional samples from `X` given `Y` is true

*source:*
[Sigma/src/query/rand.jl:43](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__dims.1" class="lexicon_definition"></a>
#### dims(X::SymbolicRandVar{T}) [¶](#method__dims.1)
Return a Set of dimension indices of a random variable

*source:*
[Sigma/src/randvar/symbolic.jl:4](file:///home/zenna/.julia/v0.3/Sigma/src/randvar/symbolic.jl)

---

<a id="method__model.1" class="lexicon_definition"></a>
#### model(X::Union(RandArray{T, N}, RandVar{T}), Y::RandVar{Bool}) [¶](#method__model.1)
Generates a 'model' from X given that Y is true, a model is like a sample
except that it does not follow any well defined distribution

*source:*
[Sigma/src/query/model.jl:36](file:///home/zenna/.julia/v0.3/Sigma/src/query/model.jl)

---

<a id="method__prob.1" class="lexicon_definition"></a>
#### prob(Y::RandVar{Bool}) [¶](#method__prob.1)
Lower and upper bounds for marginal probability that Y is true

*source:*
[Sigma/src/query/prob.jl:4](file:///home/zenna/.julia/v0.3/Sigma/src/query/prob.jl)

---

<a id="method__rangetype.1" class="lexicon_definition"></a>
#### rangetype{T}(X::RandVar{T}) [¶](#method__rangetype.1)
The type of the range of a random variable

*source:*
[Sigma/src/randvar.jl:21](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

---

<a id="type__randarray.1" class="lexicon_definition"></a>
#### RandArray{T, N} [¶](#type__randarray.1)
An array of random variables (and also a random variable itself)
`T` is the range type of elements (e.g for multivariate normal, T = Float64)
`N` is the dimensionality of array

*source:*
[Sigma/src/randvar.jl:16](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

---

<a id="type__randvar.1" class="lexicon_definition"></a>
#### RandVar{T} [¶](#type__randvar.1)
Random Variables are functions from the sample space to some other space

*source:*
[Sigma/src/randvar.jl:2](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

## Internal

---

<a id="method__abstract_cond_sample.1" class="lexicon_definition"></a>
#### abstract_cond_sample{T}(X::ExecutableRandVar{T}, Y::RandVar{Bool}, n::Integer) [¶](#method__abstract_cond_sample.1)
`n` abstract Conditional samples from `X` given `Y` is true

*source:*
[Sigma/src/query/rand.jl:54](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__abstract_omega.1" class="lexicon_definition"></a>
#### abstract_omega(n::Int64) [¶](#method__abstract_omega.1)
Build an omega of `n` dimensions

*source:*
[Sigma/src/omega.jl:33](file:///home/zenna/.julia/v0.3/Sigma/src/omega.jl)

---

<a id="method__abstract_sample.1" class="lexicon_definition"></a>
#### abstract_sample(p::SampleablePartition{D<:Domain{T}}) [¶](#method__abstract_sample.1)
Point sample from preimage - may be invalid point due to approximations

*source:*
[Sigma/src/refinement/partition.jl:40](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="method__abstract_sample_partition.1" class="lexicon_definition"></a>
#### abstract_sample_partition(Y::RandVar{Bool}, n::Integer) [¶](#method__abstract_sample_partition.1)
`n` abstract samples from preimage: Y^-1({true})

*source:*
[Sigma/src/query/rand.jl:19](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__all.1" class="lexicon_definition"></a>
#### all{N}(Xs::RandArray{Bool, N}) [¶](#method__all.1)
Is every element in Xs true, returns Bool-valued RandVar

*source:*
[Sigma/src/randvar/randarray.jl:128](file:///home/zenna/.julia/v0.3/Sigma/src/randvar/randarray.jl)

---

<a id="method__issmall.1" class="lexicon_definition"></a>
#### issmall(box::Union(LazyBox{T}, HyperBox{T}), precision::Float64) [¶](#method__issmall.1)
Is this box small (enough to be accepted)

*source:*
[Sigma/src/refinement.jl:14](file:///home/zenna/.julia/v0.3/Sigma/src/refinement.jl)

---

<a id="method__measure.1" class="lexicon_definition"></a>
#### measure(p::ApproxPartition{D<:Domain{T}}) [¶](#method__measure.1)
Lower and upper bounds for measure of partition

*source:*
[Sigma/src/refinement/partition.jl:12](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="method__ndims.1" class="lexicon_definition"></a>
#### ndims(X::RandVar{T}) [¶](#method__ndims.1)
Number of dimensions of a random variable

*source:*
[Sigma/src/randvar.jl:24](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

---

<a id="method__neverstop.1" class="lexicon_definition"></a>
#### neverstop(_...) [¶](#method__neverstop.1)
A stop function used as dummy stopping criteria in while loops

*source:*
[Sigma/src/refinement.jl:11](file:///home/zenna/.julia/v0.3/Sigma/src/refinement.jl)

---

<a id="method__point_sample.1" class="lexicon_definition"></a>
#### point_sample(chain::Array{T<:Domain{T}, 1}) [¶](#method__point_sample.1)
Get point samples out of a abstract Markov chain

*source:*
[Sigma/src/refinement/chain.jl:7](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/chain.jl)

---

<a id="method__point_sample.2" class="lexicon_definition"></a>
#### point_sample(p::SampleablePartition{D<:Domain{T}}, n::Integer) [¶](#method__point_sample.2)
`n` Point samples from preimage - may be invalid point due to approximations

*source:*
[Sigma/src/refinement/partition.jl:43](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="method__point_sample_exact.1" class="lexicon_definition"></a>
#### point_sample_exact(p::SampleablePartition{D<:Domain{T}}, Y::RandVar{Bool}) [¶](#method__point_sample_exact.1)
Do refined rejection sampling from preimage

*source:*
[Sigma/src/refinement/partition.jl:52](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="method__point_sample_mc.1" class="lexicon_definition"></a>
#### point_sample_mc(Y::RandVar{Bool}, n::Integer) [¶](#method__point_sample_mc.1)
`n` approximate point Sample from preimage: Y^-1({true})

*source:*
[Sigma/src/query/rand.jl:67](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__point_sample_partition.1" class="lexicon_definition"></a>
#### point_sample_partition(Y::RandVar{Bool}, n::Integer) [¶](#method__point_sample_partition.1)
`n` point Sample from preimage: Y^-1({true})

*source:*
[Sigma/src/query/rand.jl:29](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__pre_mc.1" class="lexicon_definition"></a>
#### pre_mc{D<:Domain{T}}(Y::RandVar{Bool}, init_box::D<:Domain{T}, niters::Integer, ::Type{AIM}) [¶](#method__pre_mc.1)
Uniform sample of subset of preimage of Y under f unioned with X.

*source:*
[Sigma/src/refinement/aim.jl:88](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/aim.jl)

---

<a id="method__preimage_model.1" class="lexicon_definition"></a>
#### preimage_model(Y::DRealRandVar{Bool}) [¶](#method__preimage_model.1)
Generates a 'model' from X given that Y is true, a model is like a sample
except that it does not follow any wel ldefined distribution

*source:*
[Sigma/src/query/model.jl:6](file:///home/zenna/.julia/v0.3/Sigma/src/query/model.jl)

---

<a id="method__proposebox_tl.1" class="lexicon_definition"></a>
#### proposebox_tl{D<:Domain{T}}(X::RandVar{T}, box::D<:Domain{T}) [¶](#method__proposebox_tl.1)
Proposes a box using refinement

*source:*
[Sigma/src/refinement/aim.jl:10](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/aim.jl)

---

<a id="method__rand.1" class="lexicon_definition"></a>
#### rand{T}(X::ExecutableRandVar{T}) [¶](#method__rand.1)
Generate an unconditioned random sample from X

*source:*
[Sigma/src/query/rand.jl:5](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="method__rand.2" class="lexicon_definition"></a>
#### rand{T}(X::ExecutableRandVar{T}, n::Integer) [¶](#method__rand.2)
Generate `n` unconditioned random samples from distribution of X

*source:*
[Sigma/src/query/rand.jl:8](file:///home/zenna/.julia/v0.3/Sigma/src/query/rand.jl)

---

<a id="type__aim.1" class="lexicon_definition"></a>
#### AIM [¶](#type__aim.1)
Abstract Independent Metropolis Sampliing samples events in preimage
uniformly in convergence of the Markov Chain.
This algorithm is useful for high dimensional problems

*source:*
[Sigma/src/refinement/aim.jl:7](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/aim.jl)

---

<a id="type__approxpartition.1" class="lexicon_definition"></a>
#### ApproxPartition{D<:Domain{T}} [¶](#type__approxpartition.1)
A partition of a set containing both an under approximation, and the rest
The rest is an overapproximation - rest

*source:*
[Sigma/src/refinement/partition.jl:6](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="type__constantrandvar.1" class="lexicon_definition"></a>
#### ConstantRandVar{T} [¶](#type__constantrandvar.1)
A constant value. A constant function which 'ignores' input, e.g. ω->5

*source:*
[Sigma/src/randvar/symbolic.jl:42](file:///home/zenna/.julia/v0.3/Sigma/src/randvar/symbolic.jl)

---

<a id="type__executablerandvar.1" class="lexicon_definition"></a>
#### ExecutableRandVar{T} [¶](#type__executablerandvar.1)
Can be excuted as a normal julia function

*source:*
[Sigma/src/randvar.jl:8](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

---

<a id="type__omegarandvar.1" class="lexicon_definition"></a>
#### OmegaRandVar{T} [¶](#type__omegarandvar.1)
Simplest RandVar: ω->ω[dim] - extracts dim component of omega

*source:*
[Sigma/src/randvar/symbolic.jl:66](file:///home/zenna/.julia/v0.3/Sigma/src/randvar/symbolic.jl)

---

<a id="type__sexpr.1" class="lexicon_definition"></a>
#### SExpr [¶](#type__sexpr.1)
A Lisp SExpr

*source:*
[Sigma/src/solver/drealbinary.jl:7](file:///home/zenna/.julia/v0.3/Sigma/src/solver/drealbinary.jl)

---

<a id="type__sampleablepartition.1" class="lexicon_definition"></a>
#### SampleablePartition{D<:Domain{T}} [¶](#type__sampleablepartition.1)
A partition which is efficient for drawing many samples.

*source:*
[Sigma/src/refinement/partition.jl:23](file:///home/zenna/.julia/v0.3/Sigma/src/refinement/partition.jl)

---

<a id="type__solver.1" class="lexicon_definition"></a>
#### Solver [¶](#type__solver.1)
Solvers inference problems.  Used mostly as an enumeration for different
inference procedures, e.g. `rand(X,Y,DRealSolver)`

*source:*
[Sigma/src/solver.jl:3](file:///home/zenna/.julia/v0.3/Sigma/src/solver.jl)

---

<a id="type__symbolicrandvar.1" class="lexicon_definition"></a>
#### SymbolicRandVar{T} [¶](#type__symbolicrandvar.1)
A symbolic *canonical* representation of a random variable

*source:*
[Sigma/src/randvar.jl:5](file:///home/zenna/.julia/v0.3/Sigma/src/randvar.jl)

---

<a id="typealias__abstractomega.1" class="lexicon_definition"></a>
#### AbstractOmega [¶](#typealias__abstractomega.1)
Abstract representations of sample space - euclidean box

*source:*
[Sigma/src/omega.jl:27](file:///home/zenna/.julia/v0.3/Sigma/src/omega.jl)

---

<a id="typealias__concreteomega.1" class="lexicon_definition"></a>
#### ConcreteOmega [¶](#typealias__concreteomega.1)
A concrete (i.e. not abstract) element ω in sample space Ω

*source:*
[Sigma/src/omega.jl:30](file:///home/zenna/.julia/v0.3/Sigma/src/omega.jl)

---

<a id="typealias__omega.1" class="lexicon_definition"></a>
#### Omega [¶](#typealias__omega.1)
All kinds of Omega

*source:*
[Sigma/src/omega.jl:24](file:///home/zenna/.julia/v0.3/Sigma/src/omega.jl)

