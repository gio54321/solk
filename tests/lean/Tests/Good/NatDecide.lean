-- `decide` builds `Nat.decLt`, which computes `Nat.ble` on literals
theorem test : 123456789 < 987654321 ∧ 2 ^ 64 ≠ 2 ^ 64 + 1 := by decide
