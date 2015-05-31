using Sigma

A = flip(1,0.3)
B = ifelse(A,3,4)
rand(A,B>3.5,1)
