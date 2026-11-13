theorem test : Nat.ble 1000000 1000001 = true ∧ Nat.ble 1000001 1000000 = false :=
  ⟨rfl, rfl⟩
