## SMT Primitive Distributions
## ===========================

std_asserts(i::Int) = Set([ω->ω_asserts(ω,i)])

## Uniform
uniformsmt(i::Int,a,b) =
  RandVarSMT{Float64}(:(($b - $a) * $(ω_nth(i)) + $a),Dict(),
             Set([ω->ω_asserts(ω,i)]),Set(i))

uniformsmt(i::Int64,a::Real,b::Real) =
  RandVarSMT{Float64}(:($(b - a) * $(ω_nth(i)) + $a),Dict(),
             Set([ω->ω_asserts(ω,i)]),Set(i))

uniformsmt(a,b) = uniformsmt(genint(),a,b)

## Normal
function normalsmt(i::Int,μ::Real,σ::Real)
  d = Normal(μ,σ)
  name = symbol("normal$i")
  asserts = Set([ω->other_asserts(ω,i,name,d)])
  RandVarSMT{Float64}(name,Dict(),asserts,Set(i))
end

normalsmt(μ,σ) = normalsmt(genint(), μ, σ)

## Bernoulli
function flipsmt(i::Int64, p::Real)
  @assert 0 <= p <= 1
  RandVarSMT{Bool}(:((>=)($p,$(ω_nth(i)))),Dict(),
                   Set([ω->ω_asserts(ω,i)]),
                   Set(i))
end

flipsmt(p::Real) = flipsmt(genint(), p)
flipsmt(i::Int) = flipsmt(i,0.5)
flipsmt() = flipsmt(genint(),0.5)
