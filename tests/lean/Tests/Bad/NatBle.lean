import Tests.Util
bad_thm test : Nat.ble 1000001 1000000 = true := Eq.refl (Nat.ble 1000001 1000000)
