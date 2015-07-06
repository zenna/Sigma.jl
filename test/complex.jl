using Sigma
A = [uniform(i,0,i) for i = 1:10]
B = [Sigma.exponential(i+10, rand()) for i = 1:10]
C = A.*B
D = ifelse(sum(C)>200,3,4)
