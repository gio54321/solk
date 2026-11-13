-- `n + 1` unfolds to `Nat.succ n`, compared with a literal successor
theorem test : ∀ n : Nat, n + 3 = Nat.succ (Nat.succ (n + 1)) := fun _ => rfl
