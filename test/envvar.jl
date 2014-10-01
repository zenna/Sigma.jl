using Sigma
import Sigma.EnvVar
using Base.Test
# Example

X = EnvVar{Set{Symbol},Interval}(IntervalEnvDict([noconstraints => Interval(3,5),
                            singleton(symbol("x>2")) => Interval(0,2)]))


pre_deepening(X > 0.5,T,Omega(Sigma.EnvVar),max_depth = 10)

Y = EnvVar{Set{Symbol},Interval}(IntervalEnvDict([noconstraints => Interval(0,1),
                                   singleton(symbol("y<2")) => Interval(0,4)]))


# Example
X = Sigma.uniform(1,4,6)
# X = Sigma.intervalenvvar(4.0,6.0)
Sigma.pre_deepening(X > 5,Sigma.T,Sigma.Omega(Sigma.EnvVar),max_depth = 10)
Y = Sigma.intervalenvvar(3.0,7.0)

C = @Iff (X > 5) [X+4,Y+5] [X-3,Y]
A = C[1]
B = C[2]
A
B
A < 5
B > 9
(A < 5) & (B > 6.5)