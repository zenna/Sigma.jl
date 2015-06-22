using Sigma

typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix

abstract Map

immutable BezierMap <: Map
  controls::Mat
end

immutable Bezier{M,N}
  k::Mat
end

function call{M,N}(b::Bezier{M,N}, u, v)
  out = 0.0
  for i = 0:n
    for j = 0:m
      out += bernstein(n,i,u)*bernstein(m,j,v)*b.controls[i,j]
    end
  end
end

bernstein(n::Integer, i::Integer, u) = binomial(n, i) * u^i * (1-u)^(n-i)
  
plot(m::BezierMap) = ...

@doc "Compute cost of path on map `m`" -> 
function cost(m::BezierMap, p::Path) end

@doc "Generate a random path `path_length` long, starting at `start_pos`" -> 
function gen_path(start_pos::Pos, path_length::Integer)
  path = RandArray(Float64, 2, path_length)
  # First position in path is at start point
  path[:,1] =  start_pos[:,1]

  # Then make path_length-1 moves
  for i = 2:path_length
    path[:,i] = path[:,i-1] + mvuniform(-1,1,2,1)
  end
  path
end

@doc "Generate condition RandVar{Bool}, true iff observed path is optimal" -> 
function optimal_cond(m::Map, observed::Path)
  optimal_cost = cost(map, observed)
  alt_path_lengths = ...
  optimal_conds = RandArray(Bool,length(alt_path_lengths))
  for i = 1:length(alternative)
    p = gen_path(alt_path_lengths[i])
    optimal_conds[i] = cost(p) >= optimal_cost
  end
  all(optimal_conds)
end

