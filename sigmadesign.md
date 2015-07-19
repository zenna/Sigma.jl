# Sigma Design

The objective of this document is to discuss the design of Sigma as a probabilistic programming library and solver.
There are two classes of existing software tools from which to draw inspiration.

# Interface to Sigma
The first class are satisfiability (particularly SMT) solvers.
Conditional sampling is very much related to getting a satisfying model from a logic formula, i.e., constraint solving.  The main differences are that i) conditional samples should be drawn from some well defined distribution ii) typically we are interested in drawing many conditional samples, and iii) probabilistic programs are often composed in a richer language (sometimes practically, sometimes theoretically) than first order logic.
Nevertheless, one option is to follow the structure of an SMT solver with some additional queries.  That is:

- Provide a sequence of commands to construct a formula
- Provide a sequence of commands to add constraints, such as `add!` and `push!` and `pop!`
- add a `sample` method, which is just like `model` in `z3` or `opensmt`, except it samples from the correct distribution.
- A more convenient interface could be built on top of this, as I have done with dReal.

## Structure Within Sigma
There are many components of Sigma.  They fundamental thing is a random variable.  In Sigma, we really only care about the distributions of Random Variables but their actual functional properties.  In other words, there are many functionally distinct but distributionally equivalent random variables.  These different random variables may even be defined on different domains, but would necessarily have the same range.  Currently in Sigma we define random variables all assuming this unit hypercube domain.  An alternative is to define random variables, or at least primitive random variables, in a manner which is agnostic towards the underlying domain

__Open Question:__ Should we define primitive random variables in a domain agnostic manner?

For example, instead of saying `uniform(i, a, b) = (b - a) * rand(i) + ` we say
`uniform(i, a, b) = Uniform(i, a, b)` where we construct this uniform type.  This could have the benefit that
- Symbolic reasoning with distributions may be easier
- We may be able to redefine the domain according to the problem and according to the solvers used.  For example if we only use discrete random variables then in some cases a discrete sample space may be more suitable.  And we may be able to more directly use solvers designed for integer programming.

## Inference Algorithms
Currently there are two classes of inference problems Sigma tries to solve:
(conditional) probability queries and (conditional) sampling.  The reality is a little more complex, because the hardness of inference means we have to approximate, and so we are actually solving approximations, of various kind, of these inference problems.  In particular:
1. Depending on the problem, we may have to solve a delta relaxed version of the inference problem
2. For conditional sampling, our samples may not be exact.  Using a Markov Chain only gives convergence guarantees.  A hashing approach may give other guarantees.

The actual algorithms we use are slightly more complex still.  We have:
__Partitioning algorithm__: bfs_partition, we produce a partition of the characteristic event of predicate.
__Box and Point Samplers__: sample boxes or points from event
__Abstract Interpretation__: Evaluate a random variable with a box as input.

Also, some of these algorithms are parameterised, e.g. __bfs__ takes as input a type of random variable.  And random variables of different type use different algorithms to perform the abstract interpretation.

So the current structure for conditional sampling is that we can have a family of algorithms to perform abstract interperation, and a bunch of algorithms that can use that abstract interpretation to generate preimage samples, and a bunch of algorithms which can account for the bias in these preimage samples.  Then we can just mix and mash them together.

However there is at least one example that does not seem to fit into this mould and it's the work we've been doing to more tightly integrate with the solver.  In particular, `tlmh` in `SigmaCxx` is not paramterised by solver (it uses interval constraint propagation only), and performs conditional sampling directly.

But that may be ok, we can just say we have different types of algorithm.
Or we might say that SigmaCxx is a special case and belongs in a different package.

__Open Question:__ How should algorithms and representations be structured.  And how, if at all, should we express the contracts between these parts?

## C++/Julia
A practical question is what language should we use.  Currently we have a mix of C++ and Julia.  SMT solvers tend to be written in C++, with a C interface and other interfaces (e.g. Python, Julia on top of that).  This has the benefit of being portable over a range of devices.

On the other hand, something like JuMP is written in Julia.  It calls to external solvers which are Julia Packages wrapping C libraries.  Perhaps the question is: is Sigma more like a solver or an interface to a solver?

Well it is both, and perhaps it may even be worth while giving the interface and solving part different names.  The reason it's not quite as clear cut as is the case (or appears to be) with JuMP, is that some of Sigma's solving routines require calling other solvers.  We can't just ship off a problem to a Sigma solver and wait for a result.

In particular, for algorithms which require we evaluate a box on some input, when we are using a SMT API we are modifying some C object stored in memory.  When we are using a binary, we use some string, or pipes.  I could imagine doing all of this in C++, i.e.
- convert SigmaAST into Z3 program
- push and pop necesary constraints to answer the right question.

Pros are that it's type safe
Cons are that it's more cumbersome to write.

There are three things I gain from using C++
- Portability
- Speed
- Multithreading


## Symbolic Transformations
There's the potential to do a lot of work before we get to numerical methods by doing symbolic transformations.  For instance we can transform expressions which suffer poorly from the dependency problem in interval arithmetic to ones without any problem.

