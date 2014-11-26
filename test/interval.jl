using Sigma
import Sigma: subsumes, overlap, makepos, ⊔, measure
using Base.Test

import Intervals

# Arithmetic Should be consistent with with MFRI interval
typealias MPFIInterval Intervals.Interval

(==)(x::Interval, y::MPFIInterval) = x.l == y.left && x.u == y.right

for i in [-2, 0, 4], j in [-2, 0, 4]
  if j >= i
    for a in [-2, 0, 4], b in [-2, 0, 4]
      if b >= a
        t = Interval(i,j) * Interval(a,b) == MPFIInterval(i,j) * MPFIInterval(a,b)
        t = Interval(i,j) - Interval(a,b) == MPFIInterval(i,j) - MPFIInterval(a,b)
        if t == false
          println("failed at, i,j = ", i," ",j)
          println(Interval(i,j) * Interval(j,i),
                  " != ", MPFIInterval(i,j) * MPFIInterval(j,j))
        end
        @assert t
      end
    end
  end
end


# Concrete Arithmetic Examples
@test Interval(3,4) + Interval(9,10) === Interval(12,14)
@test Interval(3,4) * Interval(1,2) === Interval(3,8)


@test subsumes(Interval(-5,5), Interval(-3,3))
@test subsumes(Interval(-5,5), Interval(-5,5))
@test !subsumes(Interval(-5,5), Interval(-3,10))
@test !subsumes(Interval(-5,5), Interval(10,20))

@test overlap(Interval(-5,5), Interval(-3,3))
@test overlap(Interval(-5,5), Interval(-3,10))
@test overlap(Interval(0,5), Interval(5,10))
@test !overlap(Interval(-5,5), Interval(10,20))
@test !overlap(Interval(10,20), Interval(5,-5))

@test (Interval(5,5) > Interval(5,5)) === F
@test (Interval(0,5) > Interval(5,5)) === F
@test (Interval(5,5) > Interval(0,5)) === TF

@test (Interval(0,1) > Interval(-2,-1)) === T
@test (Interval(0,1) > Interval(1,2)) === F
@test (Interval(0,1) > Interval(-1,0)) === TF
@test (Interval(0,1) > Interval(1.5,2.5)) === F

@test (Interval(-9,-3) < Interval(0,3)) === T
@test (Interval(0,1) < Interval(1,2)) === TF
@test (Interval(0,1) < Interval(-1,0)) === F
@test (Interval(1.5,2.5) < Interval(0,1)) === F

@test (Interval(0,1) >= Interval(0,0)) === T
@test (Interval(0,1) <= Interval(1,1)) === T

#abs
@test abs(Interval(-3,-1)) === Interval(1,3)
@test abs(Interval(-9,0)) === Interval(0,9)
@test abs(Interval(-10,5)) === Interval(0,10)
@test abs(Interval(0,7)) === Interval(0,7)
@test abs(Interval(0,0)) === Interval(0,0)
@test abs(Interval(2,5)) === Interval(2,5)
@test sqr(Interval(-4,4)) === Interval(0,16)

# Division
@test Interval(9,18) / Interval(2,3) === Interval(3.0,9.0)
@test flip(Interval(-10,-4)) === Interval(4,10)
@test makepos(Interval(-2,5)) === Interval(0,5)

# ⊔
@test ⊔(Interval(-3,2), Interval(10,12)) === Interval(-3,12)
@test Interval(0,0) ⊔ 1 === Interval(0,1)

@test measure(Interval(0,10)) == 10.0
