import Tests.Util
bad_thm test : Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) 50 = 101 :=
  Eq.refl (Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2) 50)
