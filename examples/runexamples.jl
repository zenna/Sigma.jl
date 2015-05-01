# Examples
println("Running examples:")
examples = readdir()
for example in examples
  println(" * $example")
  include(example)
end
