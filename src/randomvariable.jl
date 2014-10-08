typealias RandomVariable Function

# Lift primitive operators to work on random variables
# A function applied to a random variable evaluates to
# a random variable

# Binary functions
for op = (:+, :-, :*, :/, :&, :|, :$, :>, :>=, :<=, :<, :eq)
  @eval begin
    function ($op)(a::RandomVariable, b::RandomVariable)
      f(ω) = ($op)(a(ω),b(ω))
    end
    function ($op)(a::Number, b::RandomVariable)
      f(ω) = ($op)(a,b(ω))
    end
    function ($op)(a::RandomVariable, b::Number)
      f(ω) = ($op)(a(ω),b)
    end
  end
end

# Lift unary functions
for op = (:!,:sqrt,:sqr,:abs,:round)
  @eval begin
    function ($op)(a::RandomVariable)
      f(ω) = ($op)(a(ω))
    end
  end
end
