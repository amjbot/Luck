**Luck**: Lambdas under C, k?


**Tasklist**
# use stronger decoupling between project build steps (see ast.ml)
# get full testsuite compiling (prj, typ, gen, /target/ocaml, /target/sml)
# build basis library (requires gen target definitions -- target is MLton <: SML)
# build bootstrap compiler (LOC < 1000?)


1. Choose a good subset of OCaml.
2. Add on a few cheap tricks.
3. Clean up the syntax.
4. Include batteries.
5. Compile to SML.
6. Profit?


**Milestones**

    compiles | runs | version 1.0
    [x] [ ] [ ] luck ntr.lu -- command parsing
    [ ] [ ] [ ] luck ast.lu -- state and data structures
    [ ] [ ] [ ] luck prj.lu -- build process
    [ ] [ ] [ ] luck prs.lu -- lexing / parsing
    [ ] [ ] [ ] luck typ.lu -- type checking
    [ ] [ ] [ ] luck gen.lu -- code generation
    [x] [x] [ ] ocaml compiler-implementation
    [x] [ ] [ ] luck compiler-implementation
    [x] [x] [ ] ocaml backend
    [ ] [ ] [ ] standard ML backend
    [ ] [ ] [ ] ANSI C backend
    [ ] [ ] [ ] x86 backend
    [/] [/] [ ] testsuite
    [ ] [ ] [ ] system utilities
    [ ] [ ] [ ] standard library
    [ ] [ ] [ ] networking library
    [ ] [ ] [ ] filesystem library
    [ ] [ ] [ ] database library
    [ ] [ ] [ ] graphics library?
    [ ] [ ] [ ] concurrency/multi-processing library
    [ ] [ ] [ ] lexing/parsing/type-checking library
    [ ] [ ] [ ] package manager
    [ ] [ ] [ ] declarative poke/query/monitor admin library

    [ ] are ocaml/luck functionally equivalent?
    [ ] are ocaml/luck architecturally equivalent?
    [x] do error messages make sense?
    [x] do error messages show location of error?

    [ ] parametric polymorphism?
    [ ] forall quantified types?
    [ ] union types?
    [ ] tuple types?

    [ ] killer app (gravity web framework)?

