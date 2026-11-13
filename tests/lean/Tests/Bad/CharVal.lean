import Tests.Util
bad_thm test : (Char.ofNat 97).val = 98 := Eq.refl (Char.ofNat 97).val
