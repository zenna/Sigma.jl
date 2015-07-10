## Adapting from MiniSat
## =====================

"A Boolean Variable"
typealias BoolVar Int

## Literal
## =======
"A Boolean Literal: a variable or its negation"
immutable Lit
  x::BoolVar
  Lit(var::BoolVar)= new(var)
  # Sign == true implies Lteral is negated
  Lit(var::BoolVar, sign::Bool) = new((var+var) + Int(sign))
end

# Don't use these for constructing/deconstructing literals. Use the normal constructors instead.
convert(::Type{Int},p::Lit) = p.x
~(p::Lit) = Lit(p.x $ 1)
sign(p::Lit) = Bool(p.x & 1)
var(p::Lit) = p.x >> 1
unsign(p::Lit) = Lit(p.x & ~1)
id(p::Lit, sgn::Bool) = Lit(p.x $ Int(sgn))
(<)(l1::Lit,l2::Lit) = l1.x < q.x

string(p::Lit) = sign(p) ? "-$(var(p))" : "$(var(p))"
print(io::IO, l::Lit) = print(io,string(l))
show(io::IO, l::Lit) = show(io,string(l))
# typedef int Var;
# #define var_Undef (-1)
#         bool operator <  (Lit p) const { return x < p.x;  } // '<' guarantees that p, ~p are adjacent in the ordering.


# const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
# const Lit lit_Error(var_Undef, trioue );  // }

## Lifted Booleans
## ===============
"Lifted Booleans: Bottom is added to the set"
immutable LBool
  value::Int8
end

LBool(x::Bool) = Int8(x)*2-1
($)(x::LBool,b::Bool) = Bool(b) ? Lbool(-x.value) : Lbool(x.value)

const l_true = LBool(1)
const l_false = LBool(-1)
const l_undef = LBool(0)

## Clause
## ======
"A Clause is a disjunction of literals"
immutable Clause
  # size_etc::UInt32
  # union { float act; uint32_t abst; } extra;
  data::Vector{Lit}     #data[0];
end

Clause(lits::Lit...) = Clause([lits...])

string(clause::Clause) = string(join([string(lit) for lit in clause.data]," "), " 0")
print(io::IO, clause::Clause) = print(io,string(clause))
show(io::IO, clause::Clause) = show(io,string(clause))

"A CNF is a conjunction of lcauses"
immutable CNF
  clauses::Set{Clause}
end

CNF() = CNF(Set{Clause}())
CNF(clauses::Clause...) = CNF(Set{Clause}(clauses))
union(x::CNF, y::CNF) = CNF(union(x.clauses,y.clauses))
push!(x::CNF,y::Clause) = push!(x.clauses,y)
push!(x::CNF,y::CNF) = push!(x.clauses,y.clauses...)

string(cnf::CNF) = string(join([string(cnf) for cnf in cnf.clauses],"\n"),"\n")
print(io::IO, cnf::CNF) = print(io,string(cnf))
show(io::IO, cnf::CNF) = show(io,string(cnf))


# function calc_abstraction
#     uint32_t abstraction = 0;
#   for (int i = 0; i < size(); i++)
#           abstraction |= 1 << (var(data[i]) & 31);
#   extra.abst = abstraction;  }
# end

# # This constructor cannot be used directly (doesn't allocate enough memory).
# function Clause()const V& ps, bool learnt)
#   size_etc = (ps.size() << 3) | (uint32_t)learnt;
#   for (int i = 0; i < ps.size(); i++) data[i] = ps[i];
#   if (learnt) extra.act = 0; else calcAbstraction();
# end

# # use this function instead:
# # // template<class V>
# function friend Clause* Clause_new{T}(const V& ps, bool learnt)
# end

# size(c::Clause) = size_etc >> 3
# shrink!(c::Clause,i::Int) = (assert(i <= c.size()); c.size_etc = (((c.size_etc >> 3) - i) << 3) | (c.size_etc & 7)
# pop!(c::Clause) = shrink(1)
# learnt(c::Clause) = c.size_etc & 1
# mark!(c::Clause) = (c.size_etc >> 1) & 3
# mark!(c::Clause, m::uint32_t) = c.size_etc = (c.size_etc & ~6) | ((m & 3) << 1)
# last(c::Clause) = data[size()-1]


# # NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
# # subsumption operations to behave correctly.
# getindex(c::Clause,i::Int) =  c.data[i]
# float&       activity    ()              { return extra.act; }
# uint32_t     abstraction () const { return extra.abst; }

# Lit          subsumes    (const Clause& other) const;
# void         strengthen  (Lit p);



# public:


#         // -- use this function instead:
#         // template<class V>
#         // friend Clause* Clause_new(const V& ps, bool learnt);


#         // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
#         //       subsumption operations to behave correctly.
#         Lit&         operator [] (int i)         { return data[i]; }
#         Lit          operator [] (int i) const   { return data[i]; }
#         operator const Lit* (void) const         { return data; }

#         float&       activity    ()              { return extra.act; }
#         uint32_t     abstraction () const { return extra.abst; }

#         Lit          subsumes    (const Clause& other) const;
#         void         strengthen  (Lit p);
# };

# template<class V>
# Clause* Clause_new(const V& ps, bool learnt = false) {
#     assert(sizeof(Lit)      == sizeof(uint32_t));
#     assert(sizeof(float)    == sizeof(uint32_t));
#     void* mem = malloc(sizeof(Clause) + sizeof(uint32_t)*(ps.size()));
#     return new (mem) Clause(ps, learnt);
# }

# /*_________________________________________________________________________________________________
# |
# |  subsumes : (other : const Clause&)  ->  Lit
# |
# |  Description:
# |       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
# |       by subsumption resolution.
# |
# |    Result:
# |       lit_Error  - No subsumption or simplification
# |       lit_Undef  - Clause subsumes 'other'
# |       p          - The literal p can be deleted from 'other'
# |________________________________________________________________________________________________@*/
# inline Lit Clause::subsumes(const Clause& other) const
# {
#         if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
#                 return lit_Error;

#         Lit        ret = lit_Undef;
#         const Lit* c  = (const Lit*)(*this);
#         const Lit* d  = (const Lit*)other;

#         for (int i = 0; i < size(); i++) {
#                 // search for c[i] or ~c[i]
#                 for (int j = 0; j < other.size(); j++)
#                         if (c[i] == d[j])
#                                 goto ok;
#                         else if (ret == lit_Undef && c[i] == ~d[j]){
#                                 ret = c[i];
#                                 goto ok;
#                         }

#                 // did not find it
#                 return lit_Error;
#                 ok:;
#         }

#         return ret;
# }


# inline void Clause::strengthen(Lit p)
# {
#         remove(*this, p);
#         calcAbstraction();
# }

# #endif
