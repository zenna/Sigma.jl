  using Sigma

  A = iid(Bool, i->flip(i,rand()), 1000)

  prop = rand([&, |])(A[rand(1:1000)],A[rand(1:1000)])
  for i = 1:100
    prop &= rand([&, |])(A[rand(1:1000)],A[rand(1:1000)])
  end

  to_dimacs(prop)