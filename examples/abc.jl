using Sigma

# Approximate Bayesian Computation

# http://stackoverflow.com/questions/217578/point-in-polygon-aka-hit-test
function point_in_poly(poly::Lifted{Array{Float64,2}}, testx::Float64, testy::Float64)
  nvert = size(poly,2)
  vertx = poly[1,:]
  verty = poly[2,:]
  c = false
  j = nvert
  for i = 1:nvert
    c = ifelse(((verty[i]>testy) != (verty[j]>testy)) &
               (testx < (vertx[j]-vertx[i]) *
                  (testy-verty[i]) / (verty[j]-verty[i]) + vertx[i]),
       !c,
        c)
    j = i
  end
  return c
end

# Render a polygon to a monochrome image
function render{A<:LiftedArray{Float64,2}}(poly::A, width::Int, height::Int)
  image = PureRandArray(Float64, width, height)
  for x = 1:width, y = 1:height
    image[x,y] = ifelse(point_in_poly(poly, float(x), float(y)),1.0,0.0)
  end
  image
end

# ABC comparison.
function img_compare(image::Lifted{Array{Float64,2}}, data::Array{Float64,2})
  abs(image - data)
end

## Example
## =======
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

poly = iid(Float64, i->uniform(i,0,10),2,3)
condition = sum(img_compare(render(poly,10,10),testimage)) < 5
samples = cond_sample_mh(poly, condition, 0)
