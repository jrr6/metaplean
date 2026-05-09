/-
This file is intended to serve as a (relatively) minimal and fully self-contained example of a DSL
for the simply (intrinsically) typed λ-calculus.

To keep this file fully self-contained, we forgo niceties provided elsewhere in this project (e.g.,
`nodot_inductive`, `delab_all`). Type-checking in DSL elaboration directly supervenes on Lean's
type-checking (see the "magic incantation" at the top of the elaboration section); this is
straightforward but produces quite poor error messages. We also choose to keep our AST type
"theoretically pure," meaning we do not insert any "gadgets" that help the delaborator better
pretty-print terms. Two things you might wish to do with such gadgets are:
- Store user-provided variable names at binding syntax so that the delaborator can reuse those names
  rather than defaulting to `x, y, z...`
- Have an explicit antiquotation constructor so the delaborator can produce antiquotation syntax

We use two subtle quality-of-life tricks in the elaborator:
- Calling `addTermInfo` gives us "hovers for free"
- Calling `withRef` ensures error messages span only the syntax range that produced them
-/

import Lean

/- # AST -/

inductive Typ where
  | unit
  | prod : Typ → Typ → Typ
  | arr : Typ → Typ → Typ

abbrev Context := List Typ

/-- A redefinition of `List.Mem` in `Type` (for use as de Bruijn indices). -/
inductive List.MemT (a : α) : List α → Type _ where
  | head (as : List α) : MemT a (a::as)
  | tail (b : α) {as : List α} : MemT a as → MemT a (b::as)

inductive Term : Context → Typ → Type where
  | var {Γ α} : List.MemT α Γ → Term Γ α
  | unit {Γ} : Term Γ .unit
  | pair {Γ α β} : Term Γ α → Term Γ β → Term Γ (.prod α β)
  | lam {Γ α β} : Term (α :: Γ) β → Term Γ (.arr α β)
  | app {Γ α β} : Term Γ (.arr α β) → Term Γ α → Term Γ β
  | fst {Γ α β} : Term Γ (.prod α β) → Term Γ α
  | snd {Γ α β} : Term Γ (.prod α β) → Term Γ β

/- # Concrete Syntax -/

declare_syntax_cat stlc_type
declare_syntax_cat stlc_term

syntax ident : stlc_type
syntax "unit" : stlc_type
syntax stlc_type " * " stlc_type : stlc_type
syntax stlc_type " -> " stlc_type : stlc_type
syntax "(" stlc_type ")" : stlc_type

syntax ident : stlc_term
syntax "()" : stlc_term
syntax "(" stlc_term ")" : stlc_term
syntax "(" stlc_term " : " stlc_type ")" : stlc_term
syntax "(" stlc_term ", " stlc_term ")" : stlc_term
syntax "(fn " ident " => " stlc_term ")" : stlc_term
syntax "(fn " ident " : " stlc_type " => " stlc_term ")" : stlc_term
syntax stlc_term stlc_term : stlc_term
syntax "fst " stlc_term : stlc_term
syntax "snd " stlc_term : stlc_term
syntax "#" num : stlc_term  -- raw de Bruijn indices; useful for constructing open terms
syntax "%" term:max : stlc_term  -- antiquotation mechanism (no delaborator support; see note above)

syntax "tm{ " stlc_term " }" : term
syntax "ty{ " stlc_type " }" : term

open Lean hiding Term
open Meta hiding Context

/- # Elaborator -/

section Elaboration
open Elab
open Lean.Elab.Term hiding Context

/--
A more powerful version of `mkAppM` that, in particular, will insert metavariables that can remain
unresolved upon return.

Explanation: We need to elaborate Lean terms with unresolved metavariables, which `mkAppM` does not
allow. Instead, we use the following "magic incantation" to the full-blown expression elaborator, as
suggested in [an old Zulip thread](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Unification.20and.20meta-variables.20in.20mkAppM'.html)
-/
def mkAppArgs (f : Expr) (args : Array Expr) (expTy? : Option Expr := none) :=
  elabAppArgs f #[] (args.map .expr) expTy? false false

/- ## DeBruijn Monad -/
abbrev DeBruijnT (m : Type → Type) [Monad m] := StateT (List Name) m

abbrev DeBruijnElabM := DeBruijnT TermElabM

def withBinding [Monad m] [MonadFinally m] (n : Name) (x : DeBruijnT m α) : DeBruijnT m α := do
  modify fun xs => n :: xs
  try x
  finally modify List.tail

def lookupVar [Monad m] [MonadError m] (v : Name) : DeBruijnT m Nat := do
  if let some i := (← get).idxOf? v then
    return i
  else
    monadLift (m := m) <| throwError m!"Unknown STLC identifier `{v}`"

/- ## Type Elaboration-/
partial def elabSTLCType (stx : TSyntax `stlc_type) : TermElabM Expr := do
  let rec go (stx : TSyntax `stlc_type) : TermElabM Expr := withRef stx do
    match stx with
    | `(stlc_type| unit) => return mkConst ``Typ.unit
    | `(stlc_type| $a * $b) => mkAppM ``Typ.prod #[(← go a), (← go b)]
    | `(stlc_type| $a -> $b) => mkAppM ``Typ.arr #[(← go a), (← go b)]
    | `(stlc_type| ($a)) => go a
    | stx => throwErrorAt stx m!"Unexpected syntax where STLC type expected:{indentD stx}"
  addTermInfo stx <| ← go stx

/- ## Term Elaboration -/
partial def mkExpectedElabTypeForSTLCType (stx : TSyntax `stlc_type) : TermElabM Expr := do
  let stlcTy ← elabSTLCType stx
  mkAppArgs (mkConst ``Term)
    #[(← mkFreshExprMVar (mkConst ``Context)),
      stlcTy]

def mkListMemT : Nat → (eltType : Expr) → TermElabM Expr
  | 0, eltType => do mkAppArgs (.const ``List.MemT.head [0]) #[← mkFreshExprMVar (← mkAppM ``List #[eltType])]
  | n + 1, eltType => do mkAppArgs (.const ``List.MemT.tail [0]) #[← mkFreshExprMVar eltType, ← mkListMemT n eltType]

partial def elabSTLCTerm (stx : TSyntax `stlc_term) : DeBruijnElabM Expr :=
  let rec go (stx : TSyntax `stlc_term) : DeBruijnElabM Expr := withRef stx do
    match stx with
    | `(stlc_term| $x:ident) => do
      let name := x.getId
      let idx ← lookupVar name
      mkAppArgs (mkConst ``Term.var) #[← mkListMemT idx (mkConst ``Typ)]
    | `(stlc_term| #$n) => do mkAppArgs (mkConst ``Term.var) #[← mkListMemT n.getNat (mkConst ``Typ)]
    | `(stlc_term| ()) => mkAppArgs (mkConst ``Term.unit) #[]
    | `(stlc_term| ($e)) => elabSTLCTerm e
    | `(stlc_term| ($e : $τ)) => do
      let newExpTy ← mkExpectedElabTypeForSTLCType τ
      let e ← elabSTLCTerm e
      let actTy ← inferType e
      unless (← isDefEq newExpTy actTy) do
        throwErrorAt τ m!"Type annotation does not match inferred type: \
          inferred{indentExpr actTy}\nbut annotation requires{indentExpr newExpTy}"
      return e
    | `(stlc_term| ($e, $e')) => do mkAppArgs (mkConst ``Term.pair) #[← elabSTLCTerm e, ← elabSTLCTerm e']
    | `(stlc_term| (fn $x => $e)) => withBinding x.getId do mkAppArgs (mkConst ``Term.lam) #[← elabSTLCTerm e]
    | `(stlc_term| (fn $x : $τ => $e)) => withBinding x.getId do
      elabAppArgs (mkConst ``Term.lam) #[{ ref := τ, name := `α, val := .expr <| ← elabSTLCType τ }]
                                      #[.expr <| ← elabSTLCTerm e] none false false
    | `(stlc_term| $e $e') => do mkAppArgs (mkConst ``Term.app) #[← elabSTLCTerm e, ← elabSTLCTerm e']
    | `(stlc_term| fst $e) => do mkAppArgs (mkConst ``Term.fst) #[← elabSTLCTerm e]
    | `(stlc_term| snd $e) => do mkAppArgs (mkConst ``Term.snd) #[← elabSTLCTerm e]
    | `(stlc_term| %$e) => do elabTerm e (mkAppN (mkConst ``Term) #[← mkFreshExprMVar (mkConst ``Context), ← mkFreshExprMVar (mkConst ``Typ)])
    | stx => throwError m!"Unexpected syntax where STLC term expected:{indentD stx}"
  do addTermInfo stx <| ← go stx

/- ## Embedding Syntax Elaboration -/
elab_rules : term
  | `(tm{ $tm }) => do
    let e ← elabSTLCTerm tm |>.run' []
    let expectedType ← mkAppM ``Term #[← mkListLit (mkConst ``Typ) [], ← mkFreshExprMVar (mkConst ``Typ)]
    let e ← elabAppArgs e #[] #[] expectedType false false
    instantiateMVars e
  | `(ty{ $ty }) => elabSTLCType ty

end Elaboration

/- # Delaborator -/
section Delaboration

open PrettyPrinter Delaborator SubExpr

partial def delabSTLCType (e : Expr) : DelabM (TSyntax `stlc_type) :=
  match_expr e with
  | Typ.unit => `(stlc_type| unit)
  | Typ.arr α β => do `(stlc_type| $(← delabSTLCType α) -> $(← delabSTLCType β))
  | Typ.prod α β => do `(stlc_type| $(← delabSTLCType α) * $(← delabSTLCType β))
  | _ => failure

abbrev DeBruijnDelabM := DeBruijnT DelabM

partial def delabSTLCTerm (e : Expr) : DeBruijnDelabM (TSyntax `stlc_term) :=
  match_expr e with
  | Term.var _Γ _α e => do
    let rec deBruijnIdx (pf : Expr) : Nat :=
      match_expr pf with
        | List.MemT.tail _α _a _b _as subpf => deBruijnIdx subpf + 1
        | _ => 0
    let idx := deBruijnIdx e
    if let some nm := (← get)[idx]? then
      `(stlc_term| $(mkIdent nm):ident)
    else
      `(stlc_term| #$(Syntax.mkNumLit (toString idx)))
  | Term.unit _Γ => `(stlc_term| ())
  | Term.pair _Γ _α _β e e' => do `(stlc_term| ($(← delabSTLCTerm e), $(← delabSTLCTerm e')))
  | Term.lam _Γ α _β e => do
    -- If you stored variable name metadata with `Term`s, you could use the original names here
    let varChar : Char :=
      (← get).head?
        |>.bind (·.toString.startPos.get?)
        |>.map (fun lastName => ⟨97 + (lastName.val - 97) % 26,
          by simp only [UInt32.isValidChar, UInt32.toNat_add, UInt32.reduceToNat, UInt32.toNat_mod]; omega⟩)
        |>.getD 'x'
    let varName := varChar.toString.toName
    let bodyE ← withBinding varName <| delabSTLCTerm e
    let tpE ← delabSTLCType α
    `(stlc_term| (fn $(mkIdent varName) : $tpE => $bodyE))
  | Term.app _Γ _α _β f a => do `(stlc_term| $(← delabSTLCTerm f) $(← delabSTLCTerm a))
  | Term.fst _Γ _α _β e => do `(stlc_term| fst $(← delabSTLCTerm e))
  | Term.snd _Γ _α _β e => do `(stlc_term| snd $(← delabSTLCTerm e))
  | _ => failure

@[delab app.Typ.unit, delab app.Typ.arr, delab app.Typ.prod] def delabTyp : Delab := do
  let e ← getExpr
  `(ty{ $(← delabSTLCType e) })

@[app_delab Term.var, app_delab Term.unit, app_delab Term.pair, app_delab Term.lam,
  app_delab Term.app, app_delab Term.fst, app_delab Term.snd]
def delabTerm : Delab := do
  let e ← getExpr
  `(tm{ $(← delabSTLCTerm e |>.run' []) })

end Delaboration

/- # Demo -/

def foo := tm{ (fn x : unit * unit => fst (snd x, ())) }
/-- info: foo : Term [] (ty{ unit * unit -> unit }) -/
#guard_msgs in
#check foo

/-- info: foo.app tm{ ((), ()) } : Term [] ty{ unit } -/
#guard_msgs in
#check tm{ %foo ((), ()) }
