import Tests.Util
bad_thm test : (5 : Nat) = Nat.succ (Nat.succ Nat.zero) := Eq.refl 5
