using Sigma

## 1D Ising Model
## ==============
nbits = 10
bits = RandArray([flip() for i = 1:nbits])
noisyeq(a,b) = flip(ifelse(a == b, 1.0, 0.2))

ising_condition = (&)(map(noisyeq, bits[2:end], bits[1:end-1])...)
rand(bits, ising_condition,1)