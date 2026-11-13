-- modulo zero is the identity
theorem test : (123456789 % 1000 = 789) ∧ ((10 : Nat) % 0 = 10) := ⟨rfl, rfl⟩
