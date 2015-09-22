## Compatability for julia0.3
## ==========================

immutable Logic
  val::Int8
end

 const qf_uf = Logic(0)         # Uninterpreted Functions
 const qf_nra = Logic(1)        # Non-Linear Real Arithmetic
 const qf_nra_ode = Logic(2)    # Non-Linear Real Arithmetic
 const qf_bv = Logic(3)         # BitVectors
 const qf_rdl = Logic(4)        # Real difference logics
 const qf_idl = Logic(5)        # Integer difference logics
 const qf_lra = Logic(6)        # Real linear arithmetic
 const qf_lia = Logic(7)        # Integer linear arithmetic
 const qf_ufidl = Logic(8)      # UF + IDL
 const qf_uflra = Logic(9)      # UF + LRA
 const qf_bool = Logic(10)      # Only booleans
 const qf_ct = Logic(11)        # Costqf