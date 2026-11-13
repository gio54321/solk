import Tests.Util
-- division by zero is zero
bad_thm test : (10 : Nat) / 0 = 10 := Eq.refl ((10 : Nat) / 0)
