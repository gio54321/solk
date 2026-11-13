import Lean
open Lean Elab Command Term

/--
`bad_thm test : type := value` adds the theorem `test` without checking it with the kernel,
so that its export can be used as a test that must be rejected. The value is elaborated on its
own (not against `type`), e.g. `Eq.refl (2 + 2)` for a wrong `type` such as `2 + 2 = 5`.
-/
elab "bad_thm " name:ident " : " type:term " := " value:term : command => liftTermElabM do
  let type ← elabTerm type none
  let value ← elabTerm value none
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwError "bad_thm: could not fully elaborate the type or the value"
  withOptions (debug.skipKernelTC.set · true) do
    addDecl (.thmDecl { name := name.getId, levelParams := [], type, value })
