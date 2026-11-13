-- would be hopeless in unary
set_option exponentiation.threshold 2000 in
theorem test : 2 ^ 1000 % 7 = 2 := rfl
