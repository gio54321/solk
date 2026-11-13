-- literals as indices of an inductive family
inductive V : Nat → Type where
  | nil : V 0
  | cons : V n → V (n + 1)
def test : V 3 := .cons (.cons (.cons .nil))
