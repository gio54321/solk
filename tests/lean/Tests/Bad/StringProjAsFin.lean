import Lean
open Lean
-- a string literal is not a `Fin`
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``Nat,
  value := .proj ``Fin 0 (mkStrLit "a"), hints := .opaque, safety := .safe })
