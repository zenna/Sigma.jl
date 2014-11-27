using Base.Test
using Sigma
using Gadfly

## Plotting on a circle
## ====================

X = uniform(0,1)
Y = uniform(0,1)
XY = PureRandArray([X,Y])
oncircle = (sqr(X) + sqr(Y) < 0.4) & (sqr(X) + sqr(Y) ≊ 0.399)
samples = cond_sample_mh(XY,oncircle,10;max_iters = 1000)
x = [sample[1] for sample in samples]
y = [sample[2] for sample in samples]
plot(x = x, y = y, Coord.cartesian(fixed=true))
