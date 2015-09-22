typealias opensmt_expr Ptr{Void}
typealias opensmt_context Ptr{Void}

## Communication APIs
## =========================
opensmt_init() = ccall( (:opensmt_init, "libdreal"), Void, ())

opensmt_set_verbosity(ctx::opensmt_context, level::Cint) =
  ccall((:opensmt_set_verbosity, "libdreal"), Void, (Ptr{Void}, Cint), ctx, level)

opensmt_set_precision(ctx::opensmt_context, p::Float64) =
  ccall( (:opensmt_set_precision, "libdreal"), Ptr{Void}, (Ptr{Void}, Float64), ctx, p)

opensmt_get_precision(ctx::opensmt_context, p::Float64) =
  ccall( (:opensmt_get_precision, "libdreal"), Ptr{Void}, (Ptr{Void}, Float64), ctx, p)

opensmt_version() =
  ccall( (:opensmt_version, "libdreal"), Ptr{UInt8}, ())

opensmt_print_expr(e::opensmt_expr) =
  ccall( (:opensmt_print_expr, "libdreal"), Void, (Ptr{Void},), e)

opensmt_mk_context(l::Cuint) =
  ccall( (:opensmt_mk_context, "libdreal"), Ptr{Void}, (Cuint,), l)

opensmt_del_context(ctx::opensmt_context) =
  ccall( (:opensmt_del_context, "libdreal"), Void, (Ptr{Void},), ctx)

opensmt_reset(ctx::opensmt_context) =
  ccall( (:opensmt_reset, "libdreal"), Void, (Ptr{Void},), ctx)

opensmt_push(ctx::opensmt_context) =
  ccall( (:opensmt_push, "libdreal"), Void, (Ptr{Void},), ctx)

opensmt_pop(ctx::opensmt_context) =
  ccall( (:opensmt_pop, "libdreal"), Void, (Ptr{Void},), ctx)

opensmt_pop(ctx::opensmt_context) =
  ccall( (:opensmt_pop, "libdreal"), Void, (Ptr{Void},), ctx)

opensmt_assert(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_assert, "libdreal"), Void,
    (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_check(ctx::opensmt_context) =
  ccall((:opensmt_check, "libdreal"), Cint, (Ptr{Void},), ctx)

opensmt_check_assump(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_check_assump, "libdreal"), Cuint, (Ptr{Void},Ptr{Void}), ctx, e)

opensmt_check_lim_assump(ctx::opensmt_context, e::opensmt_expr, i::Cuint) =
  ccall((:opensmt_check_assump, "libdreal"), Cuint, (Ptr{Void},Ptr{Void}), ctx, e, i)

opensmt_conflicts(ctx::opensmt_context) =
  ccall((:opensmt_conflicts, "libdreal"), Cuint, (Ptr{Void},), ctx)

opensmt_decisions(ctx::opensmt_context) =
  ccall((:opensmt_decisions, "libdreal"), Cuint, (Ptr{Void},), ctx)

opensmt_get_value(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_get_value, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_get_lb(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_get_lb, "libdreal"), Float64, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_get_ub(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_get_ub, "libdreal"), Float64, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_get_bool(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_get_bool, "libdreal"), Cint, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_prefer(e::opensmt_expr) =
  ccall((:opensmt_prefer, "libdreal"), Cuint, (Ptr{Void}, Ptr{Void}), e)

opensmt_polarity(ctx::opensmt_context, e::opensmt_expr, pos::Cint) =
  ccall((:opensmt_polarity, "libdreal"), Cuint, (Ptr{Void}, Ptr{Void}), ctx, e, pos)

opensmt_print_model(ctx::opensmt_context, c::Ptr{UInt8}) =
  ccall((:opensmt_print_model, "libdreal"), Void, (Ptr{Void}, Ptr{UInt8}), ctx, c)

opensmt_print_proof(ctx::opensmt_context, c::Ptr{UInt8}) =
  ccall((:opensmt_print_proof, "libdreal"), Void, (Ptr{Void}, Ptr{UInt8}), ctx, c)

opensmt_print_interpolant(ctx::opensmt_context, c::Ptr{UInt8}) =
  ccall((:opensmt_print_interpolant, "libdreal"), Void, (Ptr{Void}, Ptr{UInt8}), ctx, c)

## Formula Construction APIs
## =========================

opensmt_mk_true(ctx::opensmt_context) =
  ccall((:opensmt_mk_true, "libdreal"), Ptr{Void}, (Ptr{Void},), ctx)

opensmt_mk_false(ctx::opensmt_context) =
  ccall((:opensmt_mk_false, "libdreal"), Ptr{Void}, (Ptr{Void},), ctx)

opensmt_mk_bool_var(ctx::opensmt_context, varname::Ptr{UInt8}) =
  ccall((:opensmt_mk_bool_var, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_bool_var(ctx,varname::ASCIIString) = opensmt_mk_bool_var(ctx, pointer(varname))

opensmt_mk_real_var(ctx::opensmt_context, varname::ASCIIString, lb::Float64, ub::Float64) =
  ccall((:opensmt_mk_real_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}, Float64, Float64), ctx, varname, lb, ub)

opensmt_mk_int_var(ctx::opensmt_context, varname::ASCIIString, lb::Int64, ub::Int64) =
  ccall((:opensmt_mk_int_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}, Int64, Int64), ctx, varname, lb, ub)

opensmt_mk_unbounded_int_var(ctx::opensmt_context, varname::ASCIIString) =
  ccall((:opensmt_mk_unbounded_int_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_forall_int_var(ctx::opensmt_context, varname::ASCIIString, lb::Int64, ub::Int64) =
  ccall((:opensmt_mk_forall_int_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}, Int64, Int64), ctx, varname, lb, ub)

opensmt_mk_forall_unbounded_int_var(ctx::opensmt_context, varname::ASCIIString) =
  ccall((:opensmt_mk_forall_unbounded_int_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_unbounded_real_var(ctx::opensmt_context, varname::ASCIIString) =
  ccall((:opensmt_mk_unbounded_real_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_forall_real_var(ctx::opensmt_context, varname::ASCIIString, lb::Float64, ub::Float64) =
  ccall((:opensmt_mk_forall_real_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}, Float64, Float64), ctx, varname, lb, ub)

opensmt_mk_forall_unbounded_real_var(ctx::opensmt_context, varname::ASCIIString) =
  ccall((:opensmt_mk_forall_real_var, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_cost_var(ctx::opensmt_context, varname::Ptr{UInt8}) =
  ccall((:opensmt_mk_cost_var, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{UInt8}), ctx, varname)

opensmt_mk_cost_var(ctx,varname::ASCIIString) = opensmt_mk_cost_var(ctx, pointer(varname))

opensmt_mk_or(ctx::opensmt_context, es::Vector{opensmt_expr}, i::Cuint) =
  ccall((:opensmt_mk_or, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{opensmt_expr}, Cuint), ctx, es, i)

opensmt_mk_or_2(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_or_2, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_or_3(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr, e3::opensmt_expr) =
  ccall((:opensmt_mk_or_3, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2, e3)

opensmt_mk_and(ctx::opensmt_context, es::Vector{opensmt_expr}, i::Cuint) =
  ccall((:opensmt_mk_and, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{opensmt_expr}, Cuint), ctx, es, i)

opensmt_mk_and_2(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_and_2, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_and_3(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr, e3::opensmt_expr) =
  ccall((:opensmt_mk_and_3, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2, e3)

opensmt_mk_eq(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_eq, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_ite(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr, e3::opensmt_expr) =
  ccall((:opensmt_mk_ite, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2, e3)

opensmt_mk_not(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_not, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_num(ctx::opensmt_context, c::Float64) =
  ccall((:opensmt_mk_num, "libdreal"), Ptr{Void},
        (Ptr{Void}, Float64), ctx, c)

opensmt_mk_num_from_string(ctx::opensmt_context, c::ASCIIString) =
  ccall((:opensmt_mk_num_from_string, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{UInt8}), ctx, c)

opensmt_mk_plus(ctx::opensmt_context, es::Vector{opensmt_expr}, i::Cuint) =
  ccall((:opensmt_mk_plus, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{opensmt_expr}, Cuint), ctx, es, i)

opensmt_mk_plus_2(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_plus_2, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_plus_3(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr, e3::opensmt_expr) =
  ccall((:opensmt_mk_plus_3, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2, e3)

opensmt_mk_uminus(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_uminus, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_minus(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_minus, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_times(ctx::opensmt_context, es::Vector{opensmt_expr}, i::Cuint) =
  ccall((:opensmt_mk_times, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{opensmt_expr}, Cuint), ctx, es, i)

opensmt_mk_times_2(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_times_2, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_times_3(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr, e3::opensmt_expr) =
  ccall((:opensmt_mk_times_3, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2, e3)

opensmt_mk_div(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_div, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_lt(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_lt, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_leq(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_leq, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_gt(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_gt, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_geq(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_geq, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_abs(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_abs, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_exp(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_exp, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_log(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_log, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_pow(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_pow, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_sin(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_sin, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_cos(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_cos, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_tan(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_tan, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_asin(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_asin, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_acos(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_acos, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_atan(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_atan, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_sinh(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_sinh, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_cosh(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_cosh, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_tanh(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_tanh, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_atan2(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_mk_atan2, "libdreal"), Ptr{Void}, (Ptr{Void}, Ptr{Void}), ctx, e)

opensmt_mk_max(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_max, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

opensmt_mk_min(ctx::opensmt_context, e1::opensmt_expr, e2::opensmt_expr) =
  ccall((:opensmt_mk_min, "libdreal"), Ptr{Void},
        (Ptr{Void}, Ptr{Void}, Ptr{Void}), ctx, e1, e2)

## ODE
function opensmt_define_ode(
  ctx::opensmt_context, varname::ASCIIString,
  es1::Vector{opensmt_expr}, es2::Vector{opensmt_expr}, n::Cuint)
  ccall((:opensmt_define_ode, "libdreal"),
        Void,
        (Ptr{Void},Ptr{UInt8}, Ptr{opensmt_expr}, Ptr{opensmt_expr}, Cuint),
        ctx, varname, es1, es2, n)
end

function opensmt_mk_integral(
  ctx::opensmt_context,
  vars_t::Vector{opensmt_expr},
  time_l::opensmt_expr,
  time_u::opensmt_expr,
  vars_0::Vector{opensmt_expr},
  n::Cuint,
  flowname::ASCIIString)
  ccall((:opensmt_mk_integral, "libdreal"),
        Ptr{Void},
        (Ptr{Void}, Ptr{opensmt_expr}, Ptr{Void}, Ptr{Void}, Ptr{opensmt_expr}, Cuint,
        Ptr{UInt8}),
        ctx, vars_t, time_l, time_u, vars_0, n, flowname)
end

opensmt_get_model_logprob(ctx::opensmt_context, e::opensmt_expr) =
  ccall((:opensmt_get_model_logprob, "libdreal"), Float64, (Ptr{Void}, Ptr{Void}), ctx, e)
