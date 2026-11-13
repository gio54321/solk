import Tests.Util
-- the literal "ab" is not the string made of the bytes of "ac"
bad_thm test : "ab" = String.ofByteArray "ac".toByteArray "ac".isValidUTF8 := Eq.refl "ab"
