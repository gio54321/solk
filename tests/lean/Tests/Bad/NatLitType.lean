import Lean
open Lean
-- a nat literal is not a string
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``String, value := mkNatLit 5,
  hints := .opaque, safety := .safe })
