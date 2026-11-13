import Tests.Util
-- modulo zero is the identity
bad_thm test : (10 : Nat) % 0 = 0 := Eq.refl ((10 : Nat) % 0)
