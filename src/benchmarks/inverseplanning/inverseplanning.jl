using Sigma

type Terrain
  cost::Float64
end

start_location = 45
exist_state = 0
objects = [36, 47]
object_types = [0, 1]
object_names = [:A, :B]

exp_λ = 0.1

[1 1 1 1 1 1 1
 1 1 1 1 1 1 1
 1 1 2 2 2 2 2
 0 0 0 0 2 2 2
 0 0 0 0 2 2 2
 0 0 0 0 0 0 0]

[1 0 0x
 1 1 0
 1 0 0x]
Terrains = PureRandArray([])

for 