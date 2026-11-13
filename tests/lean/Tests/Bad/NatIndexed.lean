import Tests.Util
inductive V : Nat → Type where
  | nil : V 0
  | cons : V n → V (n + 1)
bad_def test : V 2 := (V.cons (V.cons (V.cons V.nil)) : V 3)
