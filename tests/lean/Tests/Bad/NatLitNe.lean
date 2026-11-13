import Tests.Util
-- different literals are different, however large
bad_thm test : 100000000000000000000 = 100000000000000000001 := Eq.refl 100000000000000000000
