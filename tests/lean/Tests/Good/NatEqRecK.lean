-- K-like reduction: `h : 5 = 2 + 3` is `Eq.refl 5`, because `2 + 3` computes to `5`
theorem test : ∀ h : (5 : Nat) = 2 + 3, @Eq.rec Nat 5 (fun _ _ => Nat) 7 (2 + 3) h = 7 :=
  fun _ => rfl
