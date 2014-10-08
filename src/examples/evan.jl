using Sigma

X = uniform(0,0,10)
Y = uniform(1,0,10)

T1 = uniform(2,0, 20)
T2 = uniform(3,0, 20)

time1 = 7/4 * X
time2 = @If((X < T1),time1,
            @If((T1 < X) & (X < T2), X + Y,
                T2 + 7/4 * Y))


X = Sigma.uniform(0,0,1)
Y = @If X > .5 Sigma.normal(1,0,1) Sigma.uniform(2,-2,3)
cond_prob_deep(X>.2,Y>.4)
# plot_cond_density(T2,time1 < time2, 0.,20.,n_bars = 40)
cond_prob_deep(uniform(0,))
println(cond_prob_deep(T1>10, time2 < time1,max_depth = 6))
