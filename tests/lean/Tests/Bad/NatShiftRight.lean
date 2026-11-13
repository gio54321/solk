import Tests.Util
bad_thm test : Nat.shiftRight 1024 3 = 127 := Eq.refl (Nat.shiftRight 1024 3)
