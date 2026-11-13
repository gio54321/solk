import Tests.Util
bad_thm test : Nat.beq 123456789 123456788 = true := Eq.refl (Nat.beq 123456789 123456788)
