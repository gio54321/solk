-- a string literal is `String.ofList` of its characters
theorem test : "abc" = String.ofList [(Char.ofNat 97), (Char.ofNat 98), (Char.ofNat 99)] := rfl
