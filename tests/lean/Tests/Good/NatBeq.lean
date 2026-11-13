theorem test : Nat.beq 123456789 123456789 = true ∧ Nat.beq 123456789 123456788 = false :=
  ⟨rfl, rfl⟩
