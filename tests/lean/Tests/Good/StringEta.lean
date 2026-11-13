-- structure eta on strings
theorem test : ∀ s : String, s = String.ofByteArray s.toByteArray s.isValidUTF8 := fun _ => rfl
