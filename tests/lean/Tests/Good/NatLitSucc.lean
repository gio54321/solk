-- a literal is a `Nat.succ` of its predecessor
theorem test : (5 : Nat) = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) := rfl
