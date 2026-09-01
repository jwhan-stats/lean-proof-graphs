import Mathlib

/- verified submission -/
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
      (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
  intro b
  have hdiag : ∀ e : I, r (e, e) = 1 := by
    intro e
    have hz : r (e, e) ≠ 0 := ne_of_gt (hr_pos e e)
    have h : r (e, e) * r (e, e) = r (e, e) * 1 := by
      rw [mul_one]
      exact (hr_mul e e e).symm
    exact mul_left_cancel₀ hz h
  have hinv : ∀ e d : I, (r (e, d))⁻¹ = r (d, e) := by
    intro e d
    have hone : r (e, d) * r (d, e) = 1 := by
      rw [← hdiag e]
      exact (hr_mul e e d).symm
    exact inv_eq_of_mul_eq_one_right hone
  have hsum_pos : ∀ e : I, 0 < ∑ d : I, r (d, e) := by
    intro e
    exact Finset.sum_pos (fun d _ => hr_pos d e) Finset.univ_nonempty
  have hsum_ne : ∀ e : I, (∑ d : I, r (d, e)) ≠ 0 := by
    intro e
    exact ne_of_gt (hsum_pos e)
  have hA : (∑ e : I, (∑ d : I, r (d, e))⁻¹) = 1 := by
    have hterm : ∀ e : I,
        (∑ d : I, r (d, e))⁻¹ =
          r (e, b) / (∑ d : I, r (d, b)) := by
      intro e
      calc
        (∑ d : I, r (d, e))⁻¹
            = ((∑ d : I, r (d, b)) / r (e, b))⁻¹ := by
              congr 1
              rw [div_eq_mul_inv, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d _
              calc
                r (d, e) = r (d, b) * r (b, e) := hr_mul d e b
                _ = r (d, b) * (r (e, b))⁻¹ := by rw [hinv e b]
        _ = r (e, b) / (∑ d : I, r (d, b)) := inv_div _ _
    calc
      (∑ e : I, (∑ d : I, r (d, e))⁻¹)
          = ∑ e : I, r (e, b) / (∑ d : I, r (d, b)) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hterm e
      _ = (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) := by
            rw [← Finset.sum_div]
      _ = (∑ d : I, r (d, b)) / (∑ d : I, r (d, b)) := rfl
      _ = 1 := div_self (hsum_ne b)
  have hB : (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) = 1 := by
    have hden : (∑ d : I, (r (d, b))⁻¹) = ∑ e : I, r (b, e) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hinv d b
    have hnum_pos : 0 < ∑ e : I, r (b, e) :=
      Finset.sum_pos (fun e _ => hr_pos b e) Finset.univ_nonempty
    rw [hden]
    exact div_self (ne_of_gt hnum_pos)
  have hC : (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
    have hnum : (∑ e : I, r (e, b)) = ∑ d : I, r (d, b) := rfl
    rw [hnum]
    exact div_self (hsum_ne b)
  exact ⟨hA.trans hB.symm, hB.trans hC.symm, hC⟩
