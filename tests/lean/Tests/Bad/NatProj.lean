import Lean
open Lean
-- `Nat` is not a structure
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``Nat,
  value := .proj ``Nat 0 (mkNatLit 5), hints := .opaque, safety := .safe })
