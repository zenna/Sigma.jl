## SMT Primitive Distributions
## ===========================
uniformsmt(i::Int64,a::Real,b::Real) =
  RandVarSMT{Float64}(:(($b - $a) * $(ω_nth(i)) + $a),
             Set([ω->ω_asserts(ω,i)]),Set(i))

uniformsmt(a,b) = uniformsmt(genint(),a,b)

function normalsmt(i::Int64,μ::Real,σ::Real)
  name = gensmtsym("normal$i")
  RandVarSMT{Float64}(name,
             Set([ω->normalasserts(o,i,name,Normal(μ,σ))]),
             Set(i))
end

function flipsmt(i::Int64, p::Real)
  @assert 0 <= p <= 1
  RandVarSMT{Bool}(:((>=)($p,$(ω_nth(i)))),
                   Set([ω->ω_asserts(ω,i)]),
                   Set(i))
end

flipsmt(p::Real) = flipsmt(genint(), p)
flipsmt(i::Int) = flipsmt(i,0.5)
flipsmt() = flipsmt(genint(),0.5)
