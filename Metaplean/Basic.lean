import Metaplean.Init
import Lean

/- # Judgment-Style Predicate Printing -/
section PrintRules

open Lean Meta Elab Command

/-- Executes `f` on the type of each explicit argument in the `∀` type `e`. -/
def _root_.Lean.Expr.visitForallExplicit [Monad m] [MonadControlT MetaM m]
    (f : Expr → m Unit) (e : Expr) : m Unit := visit #[] e
  where visit (fvars : Array Expr) : Expr → m Unit
    | Expr.forallE n d b c => do
      let d := d.instantiateRev fvars
      if c.isExplicit then f d
      withLocalDecl n c d fun x =>
        visit (fvars.push x) b
    | e => do
      f <| e.instantiateRev fvars

-- Copied from core
def _root_.Lean.MessageData.formatLength (ctx : PPContext) (msg : MessageData) : BaseIO Nat := do
  let { env, mctx, lctx, opts, currNamespace, openDecls } := ctx
  -- Simulate the naming context that will be added to the actual message
  let msg := MessageData.withNamingContext { currNamespace, openDecls } msg
  let fmt ← msg.format (some { env, mctx, lctx, opts })
  return fmt.pretty.length

/-- `#print_rules MyType` prints the constructors of `MyType` as inference rules. Only explicit
    arguments are rendered. -/
elab "#print_rules" id:ident : command => do
  let nm := id.getId
  let lookup? := (← getEnv).find?
  let (resolvedName, []) :: rest ← resolveGlobalName nm
    | throwUnknownConstant nm
  unless rest.isEmpty do throwError m!"Identifier `{nm}` is ambiguous"
  let some ci := lookup? resolvedName
    | throwUnknownConstant resolvedName
  unless ci.isInductive do
    throwError m!"`{.ofConstName resolvedName}` is not an inductive type"
  runTermElabM fun _ => do
  withOptions (fun o => o.setBool `pp.fieldNotation.generalized false) do
    let mut outputs : Array MessageData := #[]
    for ctor in ci.inductiveVal!.ctors do
      let ctorType := lookup? ctor |>.get!.type
      let (_, tps) ← StateT.run (s := #[]) <|
        ctorType.visitForallExplicit (m := StateT (Array MessageData) TermElabM) fun argTyp => do
          let msgData ← addMessageContext m!"{argTyp}"
          modify (·.push msgData)
      let tps := tps.map toMessageData
      let hyps := m!"    ".joinSep tps[:tps.size - 1].toList
      let resTp := tps[tps.size - 1]!
      let ppCtx : PPContext := {
        env := (← getEnv), lctx := (← getLCtx), currNamespace := (← getCurrNamespace),
        openDecls := (← getOpenDecls)
      }
      let hypsLength ← hyps.formatLength ppCtx
      let resTpLength ← resTp.formatLength ppCtx
      let sep := (max hypsLength resTpLength).fold (fun _ _ => (· ++ m!"—")) ""

      outputs := outputs.push m!"{if hypsLength = 0 then m!"" else hyps ++ m!"\n"}\
                                 {sep} {.ofConstName ctor}\n\
                                 {resTp}"
    logInfo <| m!"\n\n".joinSep outputs.toList

end PrintRules

/- # Notation Usable within Declaration -/

section DeclNotation

open Lean Parser Elab Command

/--
Defines notation that can be used in the declaration to which it expands. A block of one or more
`decl_notation` declarations must be eventually followed (after the relevant definitions) by an
`end_decl_notation` command.

The command is set up this way -- rather than, e.g., `decl_notation ... in ...` -- because we cannot
even *parse* the command in which the notation is used until after we *elaborate* the initial
notation declaration; using a construction like `in`, where the accompanying definition is parsed
as part of the same command, would cause the definition to be parsed without knowledge of the
defined notation.
-/
@[command_parser] def «declNotation» := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "decl_notation" >> optPrecedence >> optNamedName >> optNamedPrio >> many notationItem >> darrow >>
  termParser

def declNotationSecName := `_declNotationSection

elab "end_decl_notation" : command => do
  let env ← getEnv
  let entries := pendingDeclNotation.getState env
  if entries.isEmpty then
    throwError m!"There is no active `decl_notation` to end"
  if (← getScope).header != declNotationSecName.toString then
    throwError m!"`end_decl_notation` must be in the same scope as decl notation declarations. \
      If you declared an intervening section or namespace, close it before running this command."
  for stx in entries do
    elabCommand stx
  modifyEnv (pendingDeclNotation.setState · {})
  elabCommand (← `(end $(mkIdent declNotationSecName)))

elab_rules : command
  | `(declNotation|$(doc?)? $(attr?)? $[$kind?]? decl_notation $(prec?)? $(name?)? $(prio?)? $items* => $term) => do
    let hygieneIdent := mkIdent `hygiene
    let precheckIdent := mkIdent `quotPrecheck
    let localDecl ← `(set_option $hygieneIdent false in $[$doc?]? $[$attr?]? local notation $[$prec?]? $[$prio?:namedPrio]? $items* => $term)
    -- Precheck gets run too early, even though this will be elaborated in the correct environment
    let globalDecl ← `(set_option $precheckIdent false in $[$doc?]? $[$attr?]? $[$kind?]? notation $[$prec?]? $[$name?]? $[$prio?]? $items* => $term)
    if (← getScopes).any (·.header == declNotationSecName.toString) then
      elabCommand localDecl
    else
      elabCommand (← `(section $(mkIdent declNotationSecName) $localDecl:command))
    modifyEnv (pendingDeclNotation.addEntry · globalDecl)

end DeclNotation

/- # `@[pp_nodot]` for Inductive Types -/
section NoDotInductives

open Lean

initialize nodotInductiveAttr : AttributeImpl ←
  let name := `nodot_inductive
  let attrImpl : AttributeImpl := {
    ref := `nodotInductiveAttr
    name
    descr := "Applies the `[pp_nodot]` attribute to all constructors of an inductive datatype."
    applicationTime := .afterTypeChecking
    add   := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      let env ← getEnv
      let some decl := env.find? decl
        | throwError m!"Unknown declaration `{decl}`"
      unless decl.isInductive do
        throwError m!"Attribute `{stx}` can only be applied to inductive datatypes"
      -- We're forced into Boolean blindness by the design of the `ConstantInfo` API
      let ctors := decl.inductiveVal!.ctors
      for ctor in ctors do
        ppNoDotAttr.attr.add ctor stx kind
  }
  registerBuiltinAttribute attrImpl
  return attrImpl

end NoDotInductives
