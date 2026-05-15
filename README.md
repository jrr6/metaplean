# metaplean

This repository contains an assorted collection of metaprograms for programming-language formalization in Lean. These are generally hastily developed, targeted to very narrow use cases, and liable to change or break at any time.

Currently, this repository includes the following:
* A `decl_notation` command for defining notation that can be used within the body of the declaration defining that notation (so that, e.g., you can use the notation `Γ ⊢ e : τ` when defining your typing judgment)

  ```lean
  inductive Ty where
    | unit
    -- ...

  inductive Tm where
    | unit
    -- ...

  decl_notation:65 Γ " ⊢ " e " : " τ:30 => HasType Γ e τ
  inductive HasType : Tm → Ty → Prop where
    | unit : Γ ⊢ .unit : .unit
    -- ...
  end_decl_notation
  ```

* A `[nodot_inductive]` attribute that applies the `pp_nodot` attribute to every constructor of an inductive type (so that, e.g., your types pretty-print as `Ty.arr τ τ'` rather than `τ.arr τ'`)

  ```lean
  @[nodot_inductive] inductive Ty where
    | unit
    | arr : Ty → Ty → Ty
    | prod : Ty → Ty → Ty

  def t : Ty := .arr (.prod .unit .unit) .unit

  /- Without [nodot_inductive], this becomes `(Ty.unit.prod Ty.unit).arr Ty.unit` -/
  /-- info: Ty.arr (Ty.prod Ty.unit Ty.unit) Ty.unit -/
  #guard_msgs in
  #reduce t
  ```

* A `[ctors_delab]` attribute with the behavior that `@[ctors_delab Ty] def foo ...` registers `foo`
as a delaborator for every constructor of the type `Ty`

  ```lean
  import Lean

  inductive Ty where
    | unit
    | arr : Ty → Ty → Ty
    | prod : Ty → Ty → Ty

  open Lean PrettyPrinter Delaborator
  /-
  The `ctors_delab` attribute below is equivalent to
  `@[app_delab Ty.unit, app_delab Ty.arr, app_delab Ty.prod]`
  -/
  @[ctors_delab Ty] def delabTy : Delab :=
    sorry  -- Delaborator for type constructors
  ```

* An option `pp.reduce` that causes expressions to be reduced when pretty-printing, using either `whnf` or `reduceAll`

  ```lean
  set_option pp.mvars false 

  set_option pp.reduce "none"
  /-- info: id fun x => id x : ?_ → ?_ -/
  #guard_msgs in
  #check id (fun x => id x)

  set_option pp.reduce "whnf"
  /-- info: fun x => id x : ?_ → ?_ -/
  #guard_msgs in
  #check id (fun x => id x)

  set_option pp.reduce "all"
  /-- info: fun x => x : ?_ → ?_ -/
  #guard_msgs in
  #check id (fun x => id x)
  ```

* A `#print_rules` command that prints the constructors of an inductive judgment in inference-rule notation (e.g., `#print_rules MyPred`)

* A demonstration of setting up a basic DSL for the STLC in `Demo.IntrinsicallyTypedSTLC`
