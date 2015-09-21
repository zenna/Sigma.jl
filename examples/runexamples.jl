# Examples
println("Running examples:")
# examples = readdir()
examples = ["ising.jl",
            "parameterestimation.jl",
            "polynomial.jl",
            "sat.jl",
            "cancer.jl",
            "symmetry.jl",
            "nball.jl",
            "geometry.jl",
            ]
for example in examples
  println(" * $example")
  try
    include(example)
  catch e
    println("Example $example failed with error:\n $e")
  end
end
