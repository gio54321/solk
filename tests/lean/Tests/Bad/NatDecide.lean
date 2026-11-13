import Tests.Util
-- `decide` on a false proposition gives `false`, not `true`
bad_thm test : decide (987654321 < 123456789) = true := Eq.refl (decide (987654321 < 123456789))
