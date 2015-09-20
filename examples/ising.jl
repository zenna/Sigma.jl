using Sigma

## 1D Ising Model
## ==============
nbits = 10
bits = Sigma.RandArray([Sigma.flip() for i = 1:nbits])
noisyeq(a,b) = Sigma.flip(ifelse(a == b, 1.0, 0.2))

ising_condition = (&)(map(noisyeq, bits[2:end], bits[1:end-1])...)
rand(bits, ising_condition)
