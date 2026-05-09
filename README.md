# metaplean

This repository contains an assorted collection of metaprograms for programming-language formalization in Lean. These are generally hastily developed, targeted to very narrow use cases, and liable to change or break at any time.

Currently, this repository includes the following:
* A `decl_notation` command for defining notation that can be used within the body of the declaration defining that notation (so that, e.g., you can use the notation `Γ ⊢ e : τ` when defining your typing judgment)
* A `[nodot_inductive]` attribute that applies the `pp_nodot` attribute to every constructor of an inductive type (so that, e.g., your types pretty-print as `Ty.arr τ τ'` rather than `τ.arr τ'`)
* A `[ctors_delab]` attribute with the behavior that `@[ctors_delab Ty] def foo ...` registers `foo`
as a delaborator for every constructor of the type `Ty`
* A `#print_rules` command that prints the constructors of an inductive judgment in inference-rule notation
* A demonstration of setting up a basic DSL for the STLC in `Demo.IntrinsicallyTypedSTLC`
