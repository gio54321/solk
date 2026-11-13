import Tests.Util
bad_thm test : Nat.casesOn (motive := fun _ => Nat) (0 : Nat) 7 (fun _ => 8) = 8 :=
  Eq.refl (Nat.casesOn (motive := fun _ => Nat) (0 : Nat) 7 (fun _ => 8))
