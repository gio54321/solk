theorem test : Nat.casesOn (motive := fun _ => Nat) (0 : Nat) 7 (fun _ => 8) = 7 := rfl
