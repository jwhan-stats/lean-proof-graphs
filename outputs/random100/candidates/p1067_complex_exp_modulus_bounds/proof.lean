import Mathlib

/- verified submission -/
theorem complex_exp_modulus_bounds :
  let f : ℂ → ℂ := fun z => z + 1 + Complex.exp (-z)
  ∀ z : ℂ, -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3 →
    (1 / 2) * Real.exp (-z.re) ≤ ‖f z‖ ∧
      ‖f z‖ ≤ 2 * Real.exp (-z.re) := by
  intro f z hz
  have hx3 : 3 ≤ -z.re := hz.2
  have hnormz : ‖z‖ ≤ 2 * (-z.re) := by
    have h := hz.1
    nlinarith
  have hexp : 4 * (-z.re) + 2 ≤ Real.exp (-z.re) := by
    have hsum := Real.sum_le_exp_of_nonneg (show 0 ≤ -z.re by linarith) 5
    norm_num [Finset.sum_range_succ] at hsum
    nlinarith [sq_nonneg ((-z.re) - 3), sq_nonneg (-z.re)]
  have hz1 : ‖z + 1‖ ≤ (1 / 2) * Real.exp (-z.re) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le z 1
      _ = ‖z‖ + 1 := by simp
      _ ≤ (1 / 2) * Real.exp (-z.re) := by
        nlinarith [Real.exp_nonneg (-z.re)]
  have hnormexp : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    simpa using Complex.norm_exp (-z)
  have hlower_core :
      (1 / 2) * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖ := by
    have hrev := norm_sub_le_norm_add (Complex.exp (-z)) (z + 1)
    rw [hnormexp] at hrev
    have hrev' : Real.exp (-z.re) - ‖z + 1‖ ≤ ‖z + 1 + Complex.exp (-z)‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using hrev
    nlinarith [Real.exp_nonneg (-z.re)]
  have hupper_core :
      ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re) := by
    have htri := norm_add_le (z + 1) (Complex.exp (-z))
    rw [hnormexp] at htri
    nlinarith [Real.exp_nonneg (-z.re)]
  exact ⟨hlower_core, hupper_core⟩
