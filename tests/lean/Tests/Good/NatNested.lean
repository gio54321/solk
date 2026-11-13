-- arithmetic nested under other operations: the arguments are reduced first
theorem test : (2 ^ 64 - 1) % 1000 + Nat.gcd (6 * 7) (10 * 7) = 629 := rfl
