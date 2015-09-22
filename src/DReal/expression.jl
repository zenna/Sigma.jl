# @doc "a DReal typed Expression" ->
immutable Ex{T}
  e::Ptr{Void}
  vars::Set{ASCIIString}
end

no_vars() = Set{ASCIIString}()

## TODO
## Check that lb <= ub
function safe_add!(name::ASCIIString, ctx::Context)
  name ∈ ctx.vars && error("variable $name already declared within this context")
  add_vars!(ctx,name)
end

# FIXME: Way too much duplication here

# @doc "Create a variable" ->
Var(ctx::Context, T::Type{Float64}, name::ASCIIString, lb::Float64, ub::Float64) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_real_var(ctx.ctx, name, lb, ub), Set([name])))
Var(ctx::Context, T::Type{Int64}, name::ASCIIString, lb::Int32, ub::Int32) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_int_var(ctx.ctx, name, Int64(lb), Int64(ub)), Set([name])))
Var(ctx::Context, T::Type{Int64}, name::ASCIIString, lb::Int64, ub::Int64) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_int_var(ctx.ctx, name, lb, ub), Set([name])))
Var(ctx::Context, T::Type{Int64}, name::ASCIIString) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_int_var(ctx.ctx, name, typemin(Int64), typemax(Int64)),Set([name])))
Var(ctx::Context,T::Type{Bool}, name::ASCIIString) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_bool_var(ctx.ctx, name),Set([name])))

Var(ctx::Context, T::Type{Float64}, name::ASCIIString) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_unbounded_real_var(ctx.ctx, name),Set([name])))

# Global Context
Var(T, name::ASCIIString, lb, ub) = Var(global_context(), T, name, lb, ub)
Var(T, name::ASCIIString) = Var(global_context(), T, name)

# Default Name
Var{R<:Real}(ctx::Context, T::Type, lb::R, ub::R) = Var(ctx, T, genvar(), lb, ub)
Var(ctx::Context, T::Type) = Var(ctx, T, genvar())
Var{R<:Real}(T::Type, lb::R, ub::R) = Var(T, genvar(), lb, ub)
Var(T::Type) = Var(T, genvar())

ForallVar(T::Type{Float64}, lb::Float64, ub::Float64; name::ASCIIString = genvar(), ctx::Context = global_context()) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_forall_real_var(ctx.ctx, name, lb, ub), Set([name])))

ForallVar(T::Type{Float64}; name::ASCIIString = genvar(), ctx::Context = global_context()) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_forall_unbounded_real_var(ctx.ctx, name), Set([name])))

ForallVar(T::Type{Int64}, lb::Int64, ub::Int64; name::ASCIIString = genvar(), ctx::Context = global_context()) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_forall_int_var(ctx.ctx, name, lb, ub), Set([name])))

ForallVar(T::Type{Int64}; name::ASCIIString = genvar(), ctx::Context = global_context()) =
  (safe_add!(name, ctx); Ex{T}(opensmt_mk_forall_int_var(ctx.ctx, name, typemin(Int), typemax(Int)), Set([name])))
## Printing
## ========
print(io::IO, e::Ex) = opensmt_print_expr(e.e)