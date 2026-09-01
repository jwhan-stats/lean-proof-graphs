theorem finite_multiplicative_ratio_sums
    {I : Type*} [Fintype I] [Nonempty I]
    (r : I × I → ℝ)
    (hr_pos : ∀ e d : I, 0 < r (e, d))
    (hr_mul : ∀ e d b : I, r (e, d) = r (e, b) * r (b, d)) :
    ∀ b : I,
      (∑ e : I, (∑ d : I, r (d, e))⁻¹) =
          (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) ∧
      (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) =
          (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) ∧
      (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by sorry
