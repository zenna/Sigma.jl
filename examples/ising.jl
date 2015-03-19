using Sigma

## 1D Ising Model
## ==============

nbits = 10
bits = RandVarAI{Bool}[flip() for i = 1:nbits]
bits_randvar = PureRandArray(bits)
noisyeq(a,b) = flip(ifelse(a == b, 1.0, 0.2))
ising_condition = (&)(map(noisyeq, bits[2:end], bits[1:end-1])...)
cond_sample_mh(bits_randvar,ising_condition,10)