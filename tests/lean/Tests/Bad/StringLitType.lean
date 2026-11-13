import Lean
open Lean
-- a string literal is not a nat
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``Nat, value := mkStrLit "5",
  hints := .opaque, safety := .safe })
