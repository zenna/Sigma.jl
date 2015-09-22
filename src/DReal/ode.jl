"An ordinary differential equation"
immutable ODE
  var::DReal.Ex{Float64}         # independent variable
  rhs::DReal.Ex{Float64}        # f(var)
end

"A system of differential equations"
immutable ODESystem
  name::ASCIIString
  odes::Vector{ODE}
end

ODESystem(odes::Vector{ODE}) = ODESystem(genvar("flow_"), odes)

to_c{T}(exs::Vector{Ex{T}}) = [ex.e for ex in exs]

"Returns constraint that [x_1 ...] is the integral of the system of differential
equations from 0 to time_0 with initial conditions x_0 and p_0"
function integral(
  sys::ODESystem,         # a system of odes
  varst::Vector{Ex{Float64}},     # variables which will be constrained to integral output
  t0::Ex{Float64},        # lower bound of integration
  tend::Ex{Float64},      # upper bound of integration
  vars0::Vector{Ex{Float64}};     # Initial conditions
  ctx::Context=global_context())

  nvars = length(varst)
  @assert nvars == length(vars0)
  @assert nvars == length(sys.odes)
  odevars = [ode.var for ode in sys.odes]
  oderhses = [ode.rhs for ode in sys.odes]
  opensmt_define_ode(ctx.ctx, sys.name, to_c(odevars), to_c(oderhses), Cuint(length(odevars)))
  Ex{Bool}(opensmt_mk_integral(ctx.ctx, to_c(varst), t0.e, tend.e, to_c(vars0), Cuint(nvars), sys.name), no_vars())
end

function integral(
  odes::Vector{ODE},      # a system of odes
  varst::Vector{Ex{Float64}},     # variables which will be constrained to integral output
  t0::Ex{Float64},        # lower bound of integration
  tend::Ex{Float64},      # upper bound of integration
  vars0::Vector{Ex{Float64}};     # Initial conditions
  ctx::Context=global_context())

  sys = ODESystem(odes)
  integral(sys, varst, t0, tend, vars0; ctx=ctx)
end
