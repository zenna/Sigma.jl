# using Sigma
# using Lens

typealias Point AbstractVector
typealias Vec AbstractVector
typealias Mat AbstractMatrix

# Approximate Bayesian Computation

# http://stackoverflow.com/questions/217578/point-in-polygon-aka-hit-test
function point_in_poly(poly::Mat, testx::Float64, testy::Float64)
  println("Checking if point is in poly")
  print(poly)
  nvert = size(poly,2)
  vertx = poly[1,:]
  verty = poly[2,:]
  c = flip(0,0.0) # HACK
  j = nvert
  print(vertx)
  print(verty)
  print(testy)

  println("Setting up Lens")
  println("Going into Loop")
  for i = 1:nvert
    firsttest = !((verty[i]>testy) == (verty[j]>testy))
    secondtest = testx < ((vertx[j]-vertx[i]) * (testy-verty[i]) / (verty[j]-verty[i]) + vertx[i])
    conjunction = firsttest & secondtest
    c = ifelse(conjunction, !c, c)
    j = i
  end
  return c
end

# Render a polygon to a monochrome image
function render(poly::Mat, width::Int, height::Int)
  # If the point is in the polygon render it 1.0, otherwie as 0.0
  image = RandVar{Float64}[ifelse(point_in_poly(poly, float(x), float(y)),1.0,0.0)
           for x = 1:width, y = 1:height]
  PureRandArray(image)
end

# ABC comparison.
function img_compare(image::Mat, data::Mat)
  abs(image - data)
end

function abc(poly::Mat, observation::Mat)
  @show typeof(poly)
  @show poly
  width = size(observation)[1]
  height = size(observation)[2]
  rendering = render(poly,width,height)
  condition = sum(img_compare(rendering,observation)) < 5
  return poly, condition
end

## Example ABC
function test_abc()
  testimage = [0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0
               0.0 1.0 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0
               0.0 1.0 1.0 1.0 1.0 0.0 0.0 0.0 0.0 0.0
               0.0 1.0 1.0 1.0 1.0 1.0 1.0 0.0 0.0 0.0
               0.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 0.0 0.0
               0.0 1.0 1.0 1.0 1.0 1.0 1.0 0.0 0.0 0.0
               0.0 1.0 1.0 1.0 1.0 1.0 0.0 0.0 0.0 0.0
               0.0 1.0 1.0 1.0 0.0 0.0 0.0 0.0 0.0 0.0
               0.0 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0
               0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0]
  abc(mvuniform(-1,0,10,2,3),testimage)
end

poly,condition = test_abc()
ndims(condition)
to_dimacs(condition)
# rand(poly,condition,1)
