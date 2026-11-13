import Tests.Util
bad_thm test : ∀ n : Nat, Nat.succ n = 0 := fun (n : Nat) => Eq.refl (Nat.succ n)
