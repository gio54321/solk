inductive W : Nat → Type where
  | base : W 1000000
  | step : W n → W (n * 2)
def test : W 4000000 := .step (.step .base)
