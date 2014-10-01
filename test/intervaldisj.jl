using Sigma
# =============
# Example
A = [0 7
     5 8]
B = [9 10 10
     11 12 30]

X = Sigma.IntervalDisj(A)
Y = Sigma.IntervalDisj(B)
X * Y
X / Y