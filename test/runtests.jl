using Sigma

tests = ["controlflow",
         "hyperbox",
         "dreal",
         "distributions"]

println("Running tests:")

for t in tests
    test_fn = "$t.jl"
    println(" * $test_fn")
    include(test_fn)
end
