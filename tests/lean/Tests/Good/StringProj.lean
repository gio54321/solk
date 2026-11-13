import Lean
open Lean
-- a primitive projection out of a string literal
run_meta addDecl (.defnDecl {
  name := `test, levelParams := [], type := mkConst ``ByteArray,
  value := .proj ``String 0 (mkStrLit "a"), hints := .opaque, safety := .safe })
