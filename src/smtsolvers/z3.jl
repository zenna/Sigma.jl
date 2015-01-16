## Interface to Z3 (non)-linear solver
## ===================================

parse_sat_status_z3(satstatus::String) = ["sat" => SAT, "unsat" => UNSAT][strip(satstatus)]

## Library
## ========

isapprox_z3 = SExpr("(define-fun isapprox ((a Real) (b Real)) Bool
                        (<= (abs (- a b)) 0.0001))")

z3_library = [isapprox_z3]

function headerfooter_z3(program::Vector{SExpr})
  SExpr[z3_library...,
        program...,
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
  local satstatus
  try
    satstatus = parse_sat_status_z3(readall(`z3 $withext`))
  catch
    @show program.e
    error("Solver failed")
  end
  rm(withext)
  satstatus
end

const z3 = SMTSolver(headerfooter_z3, checksat_z3)
