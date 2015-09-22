# @doc """A DReal context manages all other DReal objects, global configuration options, etc.
#     Objects created in one context cannot be used in another one.""" ->
type Context
  ctx::Ptr{Void}
  vars::Set{ASCIIString}
end

Context(ctx::Ptr{Void}) = Context(ctx,Set{ASCIIString}())
Context(l::Logic) = Context(opensmt_mk_context(@compat UInt32(l.val)))

add_vars!(ctx::Context, v::Set{ASCIIString}) = push!(ctx.vars,v...)
add_vars!(ctx::Context, v::ASCIIString) = push!(ctx.vars,v)

create_global_ctx!(l::Logic = qf_nra) = 
  (global default_global_context; default_global_context = Context(l))
global_context() = (global default_global_context; default_global_context)

function set_global_ctx!(ctx::Context)
  global default_global_context
  default_global_context = ctx
end

@doc """push creates a new scope by saving the current stack size.
  A `pop` following push will undo all assertions in between""" ->
push_ctx!(ctx::Context) = opensmt_push(ctx.ctx)
push_ctx!() = push_ctx!(global_context())

@doc "Pop removes any assertion or declaration performed between it and the matching push." ->
pop_ctx!(ctx::Context) = opensmt_pop(ctx.ctx)
pop_ctx!() = pop_ctx!(global_context())

reset_ctx!(ctx::Context) = (opensmt_reset(ctx.ctx);ctx.vars = Set{ASCIIString}())
reset_ctx!() = reset_ctx!(global_context())

delete_ctx!(ctx::Context) = opensmt_del_context(ctx.ctx)
delete_ctx!() = delete_ctx!(global_context())

function reset_global_ctx!(l::Logic = qf_nra)
  delete_ctx!(global_context())
  create_global_ctx!(l)
end