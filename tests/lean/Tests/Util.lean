import Lean
open Lean Elab Command Term

/--
Elaborate `type` and `value` separately (not `value` against `type`), so that `value` may have
another type, e.g. `Eq.refl (2 + 2)` for the wrong type `2 + 2 = 5`.
-/
def elabUnchecked (type value : Syntax) : TermElabM (Expr × Expr) := do
  let type ← elabTerm type none
  let value ← elabTerm value none
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwError "could not fully elaborate the type or the value"
  return (type, value)

/-- Add `decl` without checking it with the kernel, so that it can be exported as a bad test. -/
def addUnchecked (decl : Declaration) : CoreM Unit :=
  withOptions (debug.skipKernelTC.set · true) (addDecl decl)

/-- `bad_thm test : type := value` adds the theorem `test` without checking it. -/
elab "bad_thm " name:ident " : " type:term " := " value:term : command => liftTermElabM do
  let (type, value) ← elabUnchecked type value
  addUnchecked (.thmDecl { name := name.getId, levelParams := [], type, value })

/-- `bad_def test : type := value` adds the definition `test` without checking it. -/
elab "bad_def " name:ident " : " type:term " := " value:term : command => liftTermElabM do
  let (type, value) ← elabUnchecked type value
  addUnchecked (.defnDecl {
    name := name.getId, levelParams := [], type, value, hints := .opaque, safety := .safe })
