import Lean
open Lean
-- the second field of a string is a proof, not a byte array
set_option debug.skipKernelTC true in
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``ByteArray,
  value := .proj ``String 1 (mkStrLit "a"), hints := .opaque, safety := .safe })
