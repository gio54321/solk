import Tests.Util
bad_thm test : ∀ n : Nat, n + 0 = 0 := fun (n : Nat) => Eq.refl (n + 0)
