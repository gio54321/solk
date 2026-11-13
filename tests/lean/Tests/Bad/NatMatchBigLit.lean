import Tests.Util
def pred : Nat → Nat
  | 0 => 0
  | n + 1 => n
bad_thm test : pred 100000000000 = 100000000000 := Eq.refl (pred 100000000000)
