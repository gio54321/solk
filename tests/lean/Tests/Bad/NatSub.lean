import Tests.Util
-- subtraction is truncated at zero, it does not wrap around or go negative
bad_thm test : (5 : Nat) - 7 = 1 := Eq.refl ((5 : Nat) - 7)
