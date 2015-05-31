using Sigma

A = iid(Float64, i->omega_component(i),25,525)
B = sum(A)
condition = isapprox(B,12.5)
sammple = rand(A,condition,1)
sum(sammple[1])