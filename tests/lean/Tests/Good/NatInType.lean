-- a literal computed in a type
def Vec (n : Nat) : Type := Fin (n * n + 1)
def last : Vec 1000 := (⟨1000000, by decide⟩ : Fin 1000001)
theorem test : (last : Fin 1000001).val = 1000000 := rfl
