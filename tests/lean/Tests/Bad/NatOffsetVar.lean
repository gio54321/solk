import Tests.Util
-- `n + 1` is not `n + 2`
bad_thm test : ∀ n : Nat, n + 1 = n + 2 := fun n => Eq.refl (n + 1)
