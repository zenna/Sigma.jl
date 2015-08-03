using Sigma

"Generate Spiral Constraint"
function gen_spiral(n_revolutions = 20; n_segments = 10)
  ω = Sigma.omega_component(0)
  ω_stretch = ω*2pi*n_revolutions
  x =  ω_stretch*cos(ω_stretch)
  y =  ω_stretch*sin(ω_stretch)

  segment_width = 2pi/n_segments
  segment = rand(Distributions.Uniform(0.0, 2pi))
  angle = atan(y/x)
  @show segment, segment + segment_width
  (angle > segment) & (angle < (segment + segment_width)) 
end

samples = []
for i = 1:100
  spiral_cond = gen_spiral()
  X = Sigma.uniform(0,1,0)
  condition =  (X <= 0.51)
  try
    sample = Sigma.rand(X,condition & spiral_cond,1)
    push!(samples, sample[1])
  catch e
    @show e
  end
end