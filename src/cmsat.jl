## Literal
## =======
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
sign(p::CMLit) = CMLit(@cxx sign(p.cxx))
var(p::CMLit) = CMLit(@cxx CMSat::var(p.cxx))
unsign(p::CMLit) = CMLit(@cxx unsign(p.cxx))
(==)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) == (p2.cxx);")
(!=)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) != (p2.cxx);")
(<)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) < (p2.cxx);")
(>)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) > (p2.cxx);")
(>=)(p1::CMLit, p2::CMLit) = CMLit(icxx"$(p.cxx) >= (p2.cxx);")
to_lit(p::CMLit) = CMLit(@cxx CMSat::toLit(p.cxx))
println(p::CMLit) = CMLit(icxx"std::cout << $(p.cxx) << std::endl;")

type CMClause
  cxx::Cxx.CppValue
end

function CMClause(lits::Vector{CMLit})
  clause = icxx"std::vector<CMSat::Lit>();"
  for lit in lits
    icxx"$clause.push_back($(lit.cxx));"
  end
  CMClause(clause)
end

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

# q = CMCNF()
# a = CMClause([CMLit(1,true),CMLit(1,true)])
# b = CMClause([CMLit(1,true),CMLit(1,true)])
# push!(q,q)
# length(q)


# b = icxx"$(a.cxx).size()"
# # typeof(b)
