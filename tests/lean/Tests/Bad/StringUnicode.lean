import Tests.Util
-- a code point is not its first UTF-8 byte
bad_thm test : "λ" = String.ofList [(Char.ofNat 206)] := Eq.refl "λ"
