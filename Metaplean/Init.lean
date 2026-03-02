import Lean

open Lean

/--
Env extension for storing in-declaration notation that needs to be globalized (to support
delaboration, name validation, etc.).

This cannot be declared in the main module because initializers can't be accessed in the module in
which they are declared.
-/
initialize pendingDeclNotation : SimplePersistentEnvExtension Syntax (List Syntax) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as =>
      as.foldl (· ++ ·) #[] |>.toList
    addEntryFn := fun s n => s.insert n
  }
