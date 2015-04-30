typealias Particle (D,Float64)

type Node{T}
  id::Uint64
  status::SatStatus
  data::T
end

if sat(node) == SAT
  node.counter += 1
  # go to start
elseif sat(node) == PARTIALSAT
  # Does node have sat/mixedsat children?
  if node has children
    if children end
  elseif node has no children
    node.children = split(node)
  end
end




function dls_sample{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5,
                                      max_iters = 1E3)
  status = sat(node.data)
  if satstatus == PARTIALSAT

function pre_search{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5,
                                      max_iters = 1E3)
  origin_node = Node(X, UNKNOWNSAT)
  tree = Tree(origin_node)
  for depth_limit = 1:max_depth
    println("Sample Depth Limit", depth_limit)
    tree = dls(f, Y_sub, tree, root(tree))
  end
  tree
end

function pre_importance{D <: Domain} (f::Callable, Y, X::D; box_budget = 3E5,
                                                     max_iters = 1E3)
  particles = Particle[]
  origin_node = Node(X)
  tree = Tree(origin_node)
  while length(particles) <= box_budget && i < max_iters

  end

  # Over and under approximation
  satsets = D[]
  local mixedsets
  satstatus = checksat(f,Y,X)
  if satstatus == SAT return D[X],D[]
  elseif satstatus == UNSAT return D[],D[]
  else mixedsets = D[X]
  end

  i = 0
  while length(particles) <= box_budget && i < max_iters

    println("Iteration $i : $length(boxes) boxes")
    Xsub = shift!(mixedsets)
    update_approx!(f,Xsub,Y,satsets,mixedsets)
    i += 1
  end

  if i == max_iters println("Reached Max iterations - $i")
  else println("Did $i iterations - max not reached") end
  satsets,mixedsets,ratios1,ratios2
end
