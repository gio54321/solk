-- the recursor applied to a literal
theorem test : Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) 50 = 100 := rfl
