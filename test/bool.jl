using Sigma
using Base.Test
import Sigma: overlap, subsumes, ⊔, flip, abs
import Sigma: T, F, TF

@test T & F === F
@test TF & F === F
@test T & T === T
@test TF & TF === TF
@test !T === F
@test !TF === TF
@test !F === T
@test TF | T === T
@test TF | F === TF
@test F | T === T
@test T | TF === T

# Lifted equality tests
@test (T == T) === T
@test (T == TF) === TF
@test (TF == T) === TF
@test (F == F) === T
@test (T == F) === F
@test (F == T) === F

# Overlap
@test overlap(T,F) == false
@test overlap(F,T) == false
@test overlap(T,T) == true
@test overlap(F,F) == true
@test overlap(TF,T) == true
@test overlap(T,TF) == true
@test overlap(TF,F) == true
@test overlap(F,TF) == true
@test overlap(TF,TF) == true

# Subsumes
@test subsumes(TF,F) == true
@test subsumes(TF,T) == true
@test subsumes(TF,TF) == true
@test subsumes(F,F) == subsumes(T,T) == true
@test subsumes(F,T) == subsumes(T,F) == false
@test subsumes(F,TF) == subsumes(T,TF) == false

# Join
@test ⊔(T,F) === ⊔(F,T) === TF
@test ⊔(T,T) === T
@test ⊔(F,F) === F
@test ⊔(TF,T) === ⊔(T,TF) === TF
@test ⊔(TF,F) === ⊔(F,TF) === TF
@test ⊔(TF,TF) === TF
