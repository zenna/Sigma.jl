using Sigma
Sigma.restart_counter!()
# import Base:size,getindex
typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix

dist(A,B) = sum(abs(A - B)) < 0.01

typealias Map Mat
typealias Path Mat

# Length of path
path_length(p::Path) = size(p,2)

# Comptue the cost of a path
function path_cost(p::Path, m::Map, terrain_costs::Vec)
  total_cost = 0.0
  for i = 1:path_length(p)
    @show p[1,i]
    @show p[2,i]
    terrain = m[p[1,i],p[2,i]]
    total_cost += terrain_costs[terrain]
  end
  total_cost
end

function inverse_planning(m::Map, terrain_costs::Vec, observed_path::Path)
  # Assume costs between 0 and 1
  max_cost = length(terrain_costs)
  min_cost = 0.0

  # Path Length
  plen = path_length(observed_path)
  path = mvuniform(1,max(size(m)...),2,plen)
  # path starts and ends in right place

  # Find the minimal cost
  path, dist(path,observed_path) & (path_cost(observed_path, m, terrain_costs) < 0.1)
end

# function inverse_planning_two()
#   # Choose some subset of omega
#   # This will define a subset of the terrain space
#   # Then for this subset find a subse
# end

# exp_λ = 0.1

## Maps
## =====
## Eaxmple
amap =
  [1 1 1 1 1 1 1
   1 1 1 1 1 1 1
   1 1 2 2 2 2 2
   0 0 0 0 2 2 2
   0 0 0 0 2 2 2
   0 0 0 0 0 0 0]

amap =
  [2 2 2 2 2 2 2
   2 2 2 2 2 2 2
   2 2 0 0 0 0 0
   1 1 1 1 0 0 0
   1 1 1 1 0 0 0
   1 1 1 1 1 1 1]

amap =
  [0 1 0
   1 1 0
   0 0 0
   2 0 2
   0 1 0
   0 0 0]


## Terrain Costs
terrain_costs = mvuniform(0,1,3)

## Observed Paths
## ==============
observed_path = [6 5 4 3 2 1 1 1
                 1 1 1 2 3 4 5 6]

observed_path = [6 6 6 6 6 6 6 5 4 3 2
                 1 2 3 4 5 6 7 7 7 7 7]

observed_path = [4 4 4 3 2 2 2 2 2 2
                 4 3 2 2 2 3 4 5 6 7]

observed_path = [6 5 4
                 2 2 2]

path, condition = inverse_planning(amap+1, terrain_costs, observed_path)
println("Converting into randvar")
# a = convert(Sigma.DRealRandVar{Bool}, condition)

@show dims(condition)
println("Drawing samples")
# samples = Sigma.pre_tlmh(condition, 1)

# terrains = rand(terrain_costs, condition,2,pre_tlmh, DRealSolverBinary)
# pre = Sigma.pre_tlmh_parallel(condition,10,Sigma.DRealSolverBinary;ncores=4)