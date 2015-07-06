using Sigma

# Data
λreal = 1.5

nsmall = 3
x = Sigma.mvexponential(λreal, nlarge)
datasmall = [0.08373409995125085,0.5506572107428067,2.3774576612274676]

nlarge = 20
datalarge = [1.338373415698667,0.5301637312555506,0.41538907397622316,0.7774976325057327,0.20709032803544028,0.3711121197535204,2.022784717748388,0.48809648666331956,0.09654633281139136,0.06310191055152783,0.5224825726882876,0.3787408893851342,0.29202518692889706,0.07344134820638958,0.3411194304305847,0.6360296162690621,0.23684233782641384,1.125407422095012,0.3065516430838049,0.03039760132946354]

λ = Sigma.uniform(0,2)
x = Sigma.mvexponential(λ, nsmall)
observations = x == datasmall

# Plot 1.
# No Data
prior_samples = rand(λ,1000)

## Plotting
## ========


# 1.a Histogram Prior Distribution over λ
priorhist = plot(x=prior_samples, Geom.histogram(bincount = 40))

layers = [layer(x->lambdaprior * exp(-lambdaprior* x), 0, 5,
          Theme(default_color=rand(Color.colormap("Blues")))) for lambdaprior in prior_samples[1:10]]

true_layer = layer(x->λreal * exp(-λreal* x), 0, 5,
             Theme(default_color=color("red")))

# 1.b PDF with samples from prior
priorpdf = plot(true_layer, layers..., Guide.xlabel("x"), Guide.ylabel("P(x)"))


 
posterior_samples = rand(λ, observations, 2000; RandVarType=Sigma.DRealBinaryRandVar, parallel=true)

## Prior Distribtion
plot(x=posterior_samples, Geom.histogram(bincount = 10))