-- characters are Unicode code points, encoded in UTF-8 by `String.ofList`
theorem test : "λ∀x🎉" = String.ofList [(Char.ofNat 955), (Char.ofNat 8704), (Char.ofNat 120), (Char.ofNat 127881)] := rfl
