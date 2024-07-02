import Lean
import Warmup.Scratch

open Lean Elab Command Tactic Meta

-- Our data type for holding information on theorem declarations.
structure ThmData where
  name : Name
  -- List of param_name × param_type
  params : Array (Name × Expr)
  -- LHS of the IFF
  lhs : Lean.Expr
  rhs : Lean.Expr
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

-- def matchThm (thm : TheoremVal) : Option ThmData := do
--   let (params, prf) := parseVal [] thm.value
--   match parseType thm with
--   | some (lhs, rhs) => pure { name := thm.name, params := params, lhs := lhs, rhs := rhs, prf := prf }
--   | none => none

def addVar (v : Expr) (arr : Array (Name × Expr)) : MetaM (Array (Name × Expr)) := do
    let τ ← inferType v
    match v with
    | .fvar v =>
      let nm ←  v.getUserName
      return arr.push (nm,τ)
    | _ => return arr

def collectBvars (es : Array Expr) (e : Expr) : MetaM ((Array (Name × Expr)) × Expr) := do
  let mut arr : Array (Name × Expr) := #[]
  for v in es do
    arr ← addVar v arr
  return (arr, e)


/- Note! -/
def matchIffThm' (thm : TheoremVal) : MetaM (Option ThmData) := do
  logInfo thm.type
  -- note, in general this telescope will also collect premises of implications
  let (bvars,e) ← forallTelescopeReducing thm.type (λ es e => collectBvars es e)
  match e.getAppFn with
  | .const `Iff _ =>
    let args := e.getAppArgs
    let lhs := args[0]!
    let rhs := args[1]!
    return some { name := thm.name, params := bvars, lhs := lhs, rhs := rhs, prf := thm.value}
  | _ =>
    return none

def addThmToEnv (thm : TheoremVal) : MetaM Unit := do
  match ← matchIffThm' thm with
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
            | ConstantInfo.thmInfo thm =>
                  logInfo m!"name: {thm.name}\nparams+prf: {parseVal [] thm.value}\ntype: {thm.type}"
                  addThmToEnv thm
            | _ => logError m!"Not a theorem declaration."

  }

syntax "#show_parity" : command
elab "#show_parity" : command => do
  logInfo "showing parity..."
  let decls := parityExtension.getState <| ← getEnv
  for x in decls do
    logInfo m!"---\nname: {x.name}\nparams: {x.params}\nlhs: {x.lhs}\nrhs: {x.rhs}\nprf: {x.prf}"
  return ()

-- Given `expr`, rewrite occurrences of `old` with `new`.
-- TODO: 1. doesn't work, 2. how do I handle the unknown fvar from the tagged theorem definition?
partial def rewrite_occurrences (old : Expr) (new : Expr) (expr : Expr) : MetaM Expr := do
  -- logInfo m!"old: {old}, new: {new}, expr: {expr}"
  if old == expr then
    return new
  else
    let (_, e) ← forallTelescopeReducing expr (λ es e => collectBvars es e)
    match e.getAppFn with
    | .const `Iff _ =>
      let args := e.getAppArgs
      let lhs := args[0]!
      let rhs := args[1]!
      let new_lhs <- rewrite_occurrences old new lhs
      let new_rhs <- rewrite_occurrences old new rhs
      return (Expr.app (Expr.app (Expr.const `Iff []) new_lhs) new_rhs)
    | .const `And _ =>
      let args := e.getAppArgs
      let lhs := args[0]!
      let rhs := args[1]!
      let new_lhs <- rewrite_occurrences old new lhs
      let new_rhs <- rewrite_occurrences old new rhs
      return (Expr.app (Expr.app (Expr.const `And []) new_lhs) new_rhs)
    | .const `Or _ =>
      let args := e.getAppArgs
      let lhs := args[0]!
      let rhs := args[1]!
      let new_lhs <- rewrite_occurrences old new lhs
      let new_rhs <- rewrite_occurrences old new rhs
      return (Expr.app (Expr.app (Expr.const `Or []) new_lhs) new_rhs)
    | _ => return expr
