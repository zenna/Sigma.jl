# Linear Regression Example - Same as R2 Example.
# The general idea is are looking to fit a line to some data
# Lines are described by the equation y = ax + b
# We'll assume normal distributions for the priors of a and b

dataX = [1, 2, 3, 4]
dataY = [2.02305151081547, 2.54221660051424, 3.00165586221363, 1.91956623397872]

a = normal(0,1)
b = normal(5.0, 1.82574185835055371152)
invnoise = gamma(1,1)

y = RandomArray(Float64, [normal(a*dataX[i] + b, invnoise) for i = 1:length(dataX)])
cond([a,b,invnoise],eq(y,dataY))

a = uniform(0.,1.)
rand(a)
