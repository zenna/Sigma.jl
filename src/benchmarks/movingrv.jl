using Sigma

function moving_normal(num_steps::Integer)
  function(omega)
    num_steps2 = num_steps - 1
    X = Array(Any, num_steps2 + 1)
    X[1] = normal(0,0,3)(omega)

    for i = 1:num_steps2
      X[i+1] = @If (X[i]< 10) (X[i] + 2) X[i]
    end
    X[7]
  end
end

X = moving_normal(10)
X(Omega())

# t = pre_deepening(X[end] < 10, T, Omega(), max_depth = 50)
# length(t.nodes)
plot_psuedo_density(X, 0.,20.,n_bars = 100)
prob_deep(X > 8)
Profile.print(format=:flat)
using ProfileView
plot_psuedo_density(X[2], 0., 15.,n_bars = 500)
