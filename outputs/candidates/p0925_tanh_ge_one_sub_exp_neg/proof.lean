import Mathlib

/- verified submission -/
theorem tanh_ge_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    Real.tanh x ≥ 1 - Real.exp (-x) := by
  rw [Real.tanh_eq, Real.exp_neg]
  let t : ℝ := Real.exp x
  change (t - t⁻¹) / (t + t⁻¹) ≥ 1 - t⁻¹
  have ht : 0 < t := by
    dsimp [t]
    exact Real.exp_pos x
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact Real.one_le_exp hx
  field_simp [ht.ne']
  ring_nf
  nlinarith [sq_nonneg (t - 1)]
