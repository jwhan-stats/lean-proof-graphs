theorem horseshoeLikePenalty_strictConcave (a : ℝ) (ha : 0 < a) :
    let pen_a : ℝ → ℝ := fun x => -Real.log (Real.log (1 + a / x ^ 2))
    ∀ x y t : ℝ,
      x ≠ y →
      ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) →
      0 < t →
      t < 1 →
      pen_a (t * x + (1 - t) * y) >
        t * pen_a x + (1 - t) * pen_a y := by sorry
