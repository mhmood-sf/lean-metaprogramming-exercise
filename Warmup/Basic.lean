import Lean
import Lake

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

-- Our data type for holding information on theorem declarations.
structure ThmData where
  -- Name of the theorem
  name : Name
  -- List of param_name × param_type
  params : List (Name × Name)
  -- LHS of the IFF
  lhs : Lean.Expr
  -- RHS of the IFF
  rhs : Lean.Expr
  -- The body of the theorem
  prf : Lean.Expr
  deriving BEq, Hashable

syntax (name := addParityDecl) "parity_decl" : attr

def parityDeclDesc :
  SimplePersistentEnvExtensionDescr ThmData (HashSet ThmData) := {
    addImportedFn :=
      Array.foldl (init := {}) foldArrayIntoSet
    addEntryFn := HashSet.insert
  }

-- Next, initialize the extension
initialize parityExtension : SimplePersistentEnvExtension ThmData (HashSet ThmData)
  ← registerSimplePersistentEnvExtension parityDeclDesc

-- Parse IFF expression (TODO)
def parseType (thm : TheoremVal) : Option (Expr × Expr) := match thm.type with
  | (Expr.app (Expr.app (Expr.const `Iff _) lhs) rhs) => some (lhs, rhs)
  | _ => none

-- Example: `parseVal [] thm.value`. Recursively parses and stores
-- the name+type of the params in `params`, and the rest of the function body in `body`.
def parseVal (params : List (Name × Name)) (body : Expr) : List (Name × Name) × Expr := match body with
  | Expr.lam name (.const type _) body _ => parseVal ((name, type) :: params) body
  | _ => (params, body)

def matchThm (thm : TheoremVal) : Option ThmData := do
  let (params, prf) := parseVal [] thm.value
  match parseType thm with
  | some (lhs, rhs) => pure { name := thm.name, params := params, lhs := lhs, rhs := rhs, prf := prf }
  | none => none

def addThmToEnv (thm : TheoremVal) : MetaM Unit := do
  match matchThm thm with
  | some thmData => modifyEnv fun env => parityExtension.addEntry env thmData
  | none => logError m!"Not an iff theorem."

initialize registerBuiltinAttribute {
  name := `addParityDecl
  descr := "Track theorem declarations."
  applicationTime := .afterTypeChecking
  add := fun declName stx _ => do
    let `(attr| parity_decl ) := stx
      | throwError "syntax error on : {stx}"
    MetaM.run' do
    -- get the current environment, look for the declaration which was tagged
          let e ← getEnv
          match e.find? declName with
          | none => logError m!"[@foobar] error: could not find declaration {declName} in environment"
          | some info => -- if found, update the extension
            match info with
            --| ConstantInfo.thmInfo thm => addThmToEnv thm
            | ConstantInfo.thmInfo thm => logInfo m!"name: {thm.name}\nparams+prf: {parseVal [] thm.value}\ntype: {thm.type}"
            | _ => logError m!"Not a theorem declaration."

  }

syntax "#show_parity" : command
elab "#show_parity" : command => do
  let decls := parityExtension.getState <| ← getEnv
  for x in decls do
    logInfo m!"---\nname: {x.name}\nparams: {x.params}\nlhs: {x.lhs}\nrhs: {x.rhs}\nprf: {x.prf}"
  return ()
