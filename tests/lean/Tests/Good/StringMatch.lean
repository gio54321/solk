-- match on a string literal, compiled to a decidable equality test
def greet : String → Nat
  | "hello" => 1
  | _ => 0
theorem test : greet "hello" = 1 ∧ greet "bye" = 0 := ⟨by decide, by decide⟩
