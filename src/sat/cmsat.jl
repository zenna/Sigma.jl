## Literal
## =======
@doc "A Boolean Variable" ->
typealias BoolVar Int

@doc "A Boolean Literal: a variable or its negation" ->
type CMLit
  cxx
end

CMLit(var::BoolVar, sign::Bool) = CMLit(@cxx CMSat::Lit(var, sign))

# Don't use these for constructing/deconstructing CMLit. Use the normal constructors instead.
convert(::Type{Int},p::CMLit) = p.x
to_int(p::CMLit) = @cxx p.cxx->toInt()
~(p::CMLit) = CMLit(icxx"~$(p.cxx);")
(^)(p::CMLit, b::Bool) = CMLit(icxx"$(p.cxx) ^ b;")
# (^=)(p::CMLit, b::Bool) = CMLit(icxx"$(p.cxx) ^= b;"
sign(p::CMLit) = Bool(@cxx p.cxx->sign())
var(p::CMLit) = Int(@cxx p.cxx->var())
unsign(p::CMLit) = CMLit(@cxx unsign(p.cxx))
(==)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) == (p2.cxx);")
(!=)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) != (p2.cxx);")
(<)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) < (p2.cxx);")
(>)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) > (p2.cxx);")
(>=)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) >= (p2.cxx);")
to_lit(p::CMLit) = CMLit(@cxx CMSat::toLit(p.cxx))
println(p::CMLit) = CMLit(icxx"std::cout << $(p.cxx) << std::endl;")
string(p::CMLit) = string(sign(p) ? "-" : "",var(p)+1)
print(io::IO, lit::CMLit) = print(io, string(lit))
show(io::IO, lit::CMLit) = print(io, string(lit))

## Clause
## ======

@doc "A disjunction of literals A ∨ B ∨ !C" ->
type CMClause
  cxx
end

function CMClause(lits::Vector{CMLit})
  clause = icxx"std::vector<CMSat::Lit>();"
  for lit in lits
    icxx"$clause.push_back($(lit.cxx));"
  end
  CMClause(clause)
end

getindex(clause::CMClause, i::Real) = CMLit(icxx"$(clause.cxx)[$i-1];") ## C++/Julia offset
length(clause::CMClause) = @cxx clause.cxx->size()
string(clause::CMClause) = string(join([string(clause[i]) for i = 1:length(clause)]," "), " 0")
print(io::IO, clause::CMClause) = print(io, string(clause))
show(io::IO, clause::CMClause) = print(io, string(clause))

## Conjunctive Normal Form Formula
## ===============================
type CMCNF
  cxx
end

import Base: length
CMCNF() = CMCNF(icxx"std::vector<std::vector<CMSat::Lit>>();")
function CMCNF(clauses::Vector{CMClause})
  cnf = CMCNF()
  @show cnf
  for clause in clauses
    push!(cnf, clause)
  end
  cnf
end
length(cnf::CMCNF) = @cxx cnf.cxx->size()
push!(cnf::CMCNF, clause::CMClause) = @cxx cnf.cxx->push_back(clause.cxx)
push!(cnf1::CMCNF, cnf2::CMCNF) = icxx"$(cnf1.cxx).insert($(cnf1.cxx).end(), $(cnf2.cxx).begin(), $(cnf2.cxx).end());"

getindex(cnf::CMCNF, i::Real) = CMClause(icxx"$(cnf.cxx)[$i-1];") ## C++/Julia offset
string(cnf::CMCNF) = join([string(cnf[i]) for i = 1:length(cnf)],"\n")


# print(io::IO, cnf::CMCNF) = print(io, string(cnf))
# show(io::IO, cnf::CMCNF ) = print(io, string(cnf))