import Lean

open Lean Elab Command Tactic Meta

-- Declare new syntac for the declaration attribute
syntax (name := addFooInst) "foobar" : attr

-- We first specify the types of the extension
-- Two type parameters: `α` is the type of data used to update the extention, `σ` is the type of data stored in the extension.
-- We need to specify two things: (i) how we incorporate sets/arrays of `α` (from multiple files) into a `σ`, and (ii) how we add individual `α`-terms to `σ` to the extension
-- First, let's define a helper function which incorporates an `Array` of data into an existing `HashSet`:

def foldArrayIntoSet [BEq α] [Hashable α] (s : HashSet α) (a : Array α) : HashSet α :=
  a.foldl HashSet.insert s

def fooInstDecsr :
  SimplePersistentEnvExtensionDescr Expr (HashSet Expr) := {
  addImportedFn :=
    Array.foldl (init := {}) foldArrayIntoSet
  addEntryFn := HashSet.insert
}

-- Next, initialize the extension
initialize fooExtension : SimplePersistentEnvExtension Expr (HashSet Expr)
  ← registerSimplePersistentEnvExtension fooInstDecsr

-- Now, we need to specify how the extension actually behaves from Lean syntax.

initialize registerBuiltinAttribute {
  name := `addFooInst
  descr := "Something silly ."
  applicationTime := .afterTypeChecking
  add := fun declName stx _ => do
    let `(attr| foobar ) := stx
      | throwError "syntax error on : {stx}"
    MetaM.run' do
    -- get the current environment, look for the declaration which was tagged
          let e ← getEnv
          match e.find? declName with
          | none => logError m!"[@foobar] error: could not find declaration {declName} in environment"
          | some info => -- if found, update the extension
            modifyEnv fun env =>
                fooExtension.addEntry env info.type
  }

syntax "#showFoo" : command
elab "#showFoo" : command => do
  logInfo "Printing types of declarations tagged by @[foobar]:"
  let decls := fooExtension.getState <| ← getEnv
  for x in decls do
    logInfo m!"{x}"
  return ()


-- END OF EXAMPLE
