import Tests.Util
-- a variable is not a literal
bad_thm test : ∀ n : Nat, n = 5 := fun (n : Nat) => Eq.refl n
