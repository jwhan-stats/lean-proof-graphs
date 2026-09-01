theorem reciprocal_eq_neg_one_pow_of_roots_abs_one
    (f : Polynomial ℝ) (n : ℕ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (hn : f.rootMultiplicity 1 = n) :
    f.reverse = ((-1 : ℝ) ^ n) • f := by sorry
