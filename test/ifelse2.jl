using Sigma

B = uniform(1,0,1)
C = ifelse(B>0.5,3,4) <= 3.5
rand(B,C,3)