import Tests.Util
-- `h : 5 = 2 + 2` is not `Eq.refl 5`: K-like reduction must not apply
bad_thm test : ∀ h : (5 : Nat) = 2 + 2, @Eq.rec Nat 5 (fun _ _ => Nat) 7 (2 + 2) h = 7 :=
  fun (h : (5 : Nat) = 2 + 2) => Eq.refl (@Eq.rec Nat 5 (fun _ _ => Nat) 7 (2 + 2) h)
