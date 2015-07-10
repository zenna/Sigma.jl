# Sigma

Sigma is a probabilistic programming environment implemented in Julia.
In it, you can specify probabilistic models as normal programs, and perform inference.

# Installation

Sigma is built on top of Julia.  Unless you have existing preferences, we recommend using [IJulia](https://github.com/JuliaLang/IJulia.jl) as an interface.

Sigma is not yet in the official Julia Package repository.  You can still easily install it from a Julia repl with

```julia
Pkg.clone("https://github.com/zenna/Sigma.jl.git")
```

Sigma is then loaded with

```julia
using Sigma
```