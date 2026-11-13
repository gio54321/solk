-- `match` on a big literal only peels off one `Nat.succ`
def pred : Nat → Nat
  | 0 => 0
  | n + 1 => n
theorem test : pred 100000000000 = 99999999999 := rfl
