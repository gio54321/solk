import Lean
open Lean
-- a string has only two fields
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``Nat,
  value := .proj ``String 2 (mkStrLit "a"), hints := .opaque, safety := .safe })
