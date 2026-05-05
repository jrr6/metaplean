import Lean

/-
This module contains initializer declarations that cannot be written in the main module because
initializers can't be accessed in the module in which they are declared.
-/

open Lean

/--
Env extension for storing in-declaration notation that needs to be globalized (to support
delaboration, name validation, etc.).
-/
initialize pendingDeclNotation : SimplePersistentEnvExtension Syntax (List Syntax) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as =>
      as.foldl (· ++ ·) #[] |>.toList
    addEntryFn := fun s n => s.insert n
  }

/--
An option for reducing expressions when pretty-printing. Valid values are `"off"`, `"whnf"`, and
`"all"`.
-/
register_option pp.reduce : String := {
  defValue := "none"
  descr    := "(pretty printer) reduce exprs when pretty-printing, either in \"whnf\" or \"all\""
}
