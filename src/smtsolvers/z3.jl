## Interface to Z3 (non)-linear solver
## ===================================

parse_sat_status_z3(satstatus::String) = ["sat" => SAT, "unsat" => UNSAT][strip(satstatus)]

function headerfooter_z3(program::Vector{SExpr})
  SExpr[program...,
        SExpr("(check-sat)"),
        SExpr("(exit)")]
end

## Call solver command line
## ========================
function checksat_z3(program::SExpr)
  fname = randstring()
  withext = "$fname.smt2"
  f = open(withext,"w")
  write(f,program.e)
  close(f)
  satstatus = parse_sat_status_z3(readall(`z3 $withext`))
  rm(withext)
  satstatus
end

const z3 = SMTSolver(headerfooter_z3, checksat_z3)

