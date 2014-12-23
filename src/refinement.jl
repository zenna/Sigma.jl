# Pre-image Computation:
# Given a function f:X->Y and Y' ⊆ Y -
# -- find X' ⊆ X such that f(x') ∈ Y'
## ===================================
## Iterative Deepening Preconditioning

immutable SatStatus
  status::Uint8
end

const UNSAT = SatStatus(0x0)
const SAT = SatStatus(0x1)
const PARTIALSAT = SatStatus(0x2)
const UNKNOWNSAT = SatStatus(0x3)

string(x::SatStatus) = ["UNSAT","SAT","PARTIALSAT", "UNKNOWNSAT"][x.status+1]
print(io::IO, x::SatStatus) = print(io, string(x))
show(io::IO, x::SatStatus) = print(io, string(x))
showcompact(io::IO, x::SatStatus) = print(io, string(x))

function checksat(f::Callable, Y, X::Domain)
  setimage = call(f,X)
  if subsumes(Y, setimage) SAT
  elseif overlap(setimage, Y) PARTIALSAT
  else UNSAT end
end

for finame in ["tree.jl",
               "bfs.jl",
               "mh.jl",
               "rrr.jl",
               "nrrr.jl"]
    include(joinpath("refinement", finame))
end
