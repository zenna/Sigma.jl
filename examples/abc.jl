using Sigma

# Approximate Bayesian Computation

# http://stackoverflow.com/questions/217578/point-in-polygon-aka-hit-test
function point_in_poly(poly::Lifted{Array{Float64,2}}, testx::Float64, testy::Float64)
  nvert = size(poly,2)
  vertx = poly[1,:]
  verty = poly[2,:]
  c = false
  j = nvert
  @show vertx, verty
  for i = 1:nvert
    @show testy
    @show verty[i]
    @show verty[j]
    @show !((verty[i]>testy) == (verty[j]>testy))
    @show !c
    @show c
    firsttest = !((verty[i]>testy) == (verty[j]>testy))
    secondtest = testx < ((vertx[j]-vertx[i]) * (testy-verty[i]) / (verty[j]-verty[i]) + vertx[i])
    conjunction = firsttest & secondtest
    c = ifelse(conjunction,
        !c,
        c)
    j = i
  end
  @show c
  return c
end

# Render a polygon to a monochrome image
function render{A<:LiftedArray{Float64,2}}(poly::A, width::Int, height::Int)
  image = RandVarMeta{Float64}[ifelse(point_in_poly(poly, float(x), float(y)),1.0,0.0)
           for x = 1:width, y = 1:height]
  PureRandArray(image)
end

# ABC comparison.
function img_compare(image::Lifted{Array{Float64,2}}, data::Array{Float64,2})
  abs(image - data)
end

function abc(poly, observation)
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
               0.0 1.0 0 0.0 0.0 0.0 0.0 0.0 0.0 0.0
               0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0]
  abc(mvuniformmeta(0,10,2,3),testimage)
end

# prob(ifelse(flipsmt(.3),flipsmt(.8),true))
m,c = test_abc()
cond_sample_mh(m,c,1)
