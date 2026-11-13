import Tests.Util
inductive W : Nat → Type where
  | base : W 1000000
  | step : W n → W (n * 2)
bad_def test : W 4000001 := (W.step (W.step W.base) : W 4000000)
