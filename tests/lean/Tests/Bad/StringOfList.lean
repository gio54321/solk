import Tests.Util
bad_thm test : "abc" = String.ofList [(Char.ofNat 97), (Char.ofNat 98), (Char.ofNat 100)] := Eq.refl "abc"
