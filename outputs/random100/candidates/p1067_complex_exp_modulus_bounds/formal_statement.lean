theorem complex_exp_modulus_bounds :
  let f : ℂ → ℂ := fun z => z + 1 + Complex.exp (-z)
  ∀ z : ℂ, -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3 →
    (1 / 2) * Real.exp (-z.re) ≤ ‖f z‖ ∧
      ‖f z‖ ≤ 2 * Real.exp (-z.re) := by sorry
