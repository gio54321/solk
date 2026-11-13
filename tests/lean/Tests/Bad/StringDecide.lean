import Tests.Util
bad_thm test : decide ("abc" = "abd") = true := Eq.refl (decide ("abc" = "abd"))
