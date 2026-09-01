import Mathlib

/- verified submission -/
theorem fixed_disc_of_contractivity
    {X : Type*} [MetricSpace X]
    (T : X → X) (x₀ : X) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hcontractive : ∀ x : X, dist (T x) x ≤ c * dist (T x) x₀) :
    let ρ : ℝ := sInf {r : ℝ | ∃ x : X, T x ≠ x ∧ r = dist x (T x)}
    (∀ x : X, dist x x₀ ≤ ρ → x ≠ x₀ →
      0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) →
    ∀ x : X, dist x x₀ ≤ ρ → T x = x := by
  dsimp only
  intro h x hx
  by_cases hx0 : x = x₀
  · subst x
    by_cases hdpos : 0 < dist (T x₀) x₀
    · have hlt : c * dist (T x₀) x₀ < dist (T x₀) x₀ := by
        simpa using mul_lt_mul_of_pos_right hc₁ hdpos
      exact (not_lt_of_ge (hcontractive x₀) hlt).elim
    · have hd : dist (T x₀) x₀ = 0 := by
        exact le_antisymm (not_lt.mp hdpos) dist_nonneg
      exact dist_eq_zero.mp hd
  · by_contra hTx
    let S : Set ℝ := {r : ℝ | ∃ y : X, T y ≠ y ∧ r = dist y (T y)}
    have hSbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      exact dist_nonneg
    have hSmem : dist x (T x) ∈ S := ⟨x, hTx, rfl⟩
    have hρ_le : sInf S ≤ dist x (T x) := csInf_le hSbdd hSmem
    have ha := h x hx hx0
    have hcon : dist x (T x) ≤ c * dist (T x) x₀ := by
      simpa [dist_comm] using hcontractive x
    have hlt : c * dist (T x) x₀ < dist (T x) x₀ := by
      simpa using mul_lt_mul_of_pos_right hc₁ ha.1
    have : sInf S < sInf S := by
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (le_trans hρ_le hcon) hlt)
        ha.2
    exact (lt_irrefl (sInf S) this).elim
