using Sigma
using Base.Test

import Intervals

# Should be consistent with with MFRI interval
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

# Concrete Tests
@test Interval(3,4) + Interval(9,10) == Interval(12,14)
@test sqr(Interval(-4,4)) == Interval(0,16)

# Inequalities
@test (Interval(3,4) > 3.5 ) === TF
@test (Interval(3,4) > 4 ) == false
@test (Interval(3,4) > 3 ) === TF
@test (Interval(3,4) > 2 ) == T

#abs
@test abs(Interval(-3,-1)) == Interval(1,3)
@test abs(Interval(-9,0)) == Interval(0,9)
@test abs(Interval(-10,5)) == Interval(0,10)
@test abs(Interval(0,7)) == Interval(0,7)
@test abs(Interval(0,0)) == Interval(0,0)
@test abs(Interval(2,5)) == Interval(2,5)

@test flip(Interval(-10,-4)) == Interval(4,10)
