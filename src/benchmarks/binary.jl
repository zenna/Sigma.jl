# Miscellaneous binary examples
using Sigma

import Sigma.to_intervals
sqrt(Interval(0,5))
import Sigma.sqrt
methods(sqrt)
nary_to_unary(f::Function) = x->apply(f,to_intervals(x))
## Restrict to epsilon thick circle
circle(radius, x, y) =  tolerant_eq(sqrt(sqr(x+0.001) + sqr(y-0.001)), radius, 0.1)
circle_pre = pre_deepening(nary_to_unary((x,y)->circle(5.0,x,y)), T, ndcube(-100.0,100.0,2),max_depth = 15,box_budget = typemax(Int64))
plot_2d_boxes(circle_pre)

two_halves(radius,x,y) = @If x > 0 circle(radius, x, y) circle(radius/2, x, y)
two_circles(radius,x,y) = circle(radius, x, y) | circle(radius/2, x, y)
two_circles_pre = pre_deepening(two_circles(5,0,0))

# preimage2 = pre((x,y)->two_circles(5.0,x,y), T, [ndcube(-100.0,100.0,2)],n_iters = 14)
preimage2 = pre_recursive(emilys_formula, T, [ndcube(-100.0,100.0,2)],max_depth = 15)
# preimage2 = pre(heart, T, [ndcube(-100.0,100.0,2)],n_iters = 14)

preimage_emily_deep = pre_deepening(emilys_formula,T, ndcube(-100.0,100.0,2), max_depth = 11)
preimage_emily_deep = Sigma.tree_to_boxes(preimage_emily_deep)
plot_2d_boxes(preimage_emily_deep)

