import Mathlib

/- verified submission -/
theorem cell_entropy_inequality_for_semidiscrete_finite_volume_scheme
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (N : Finset ι)
    (V : ℝ) (hV : 0 < V)
    (A δ ε : ι → ℝ)
    (hA : ∀ r ∈ N, 0 ≤ A r)
    (hδ : ∀ r ∈ N, 0 < δ r)
    (hε : ∀ r ∈ N, 0 ≤ ε r)
    (qNeighbor : ι → κ → ℝ) (q : κ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (H : ι → Matrix κ κ ℝ)
    (hH : ∀ r ∈ N, (H r).PosSemidef)
    (ρSNeighbor : ι → ℝ) (ρS : ℝ)
    (D : ι → ℝ) (dρSdt : ℝ) :
    let Δq : ι → κ → ℝ := fun r => qNeighbor r - q
    let entropyProduction : ι → ℝ := fun r =>
      ε r * dotProduct (Δq r) ((H r).mulVec (Δq r)) / (2 * T * δ r)
    let g : ι → ℝ := fun r => ε r * (ρSNeighbor r - ρS) / δ r
    dρSdt = (1 / V) * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) →
      dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r ≥ 0 := by
  intro Δq entropyProduction g hd
  have hprod : ∀ r ∈ N, 0 ≤ entropyProduction r := by
    intro r hr
    have hquad : 0 ≤ dotProduct (Δq r) ((H r).mulVec (Δq r)) := by
      simpa using (hH r hr).dotProduct_mulVec_nonneg (Δq r)
    have hden : 0 < 2 * T * δ r := by
      exact mul_pos (mul_pos (by norm_num) hT) (hδ r hr)
    exact div_nonneg (mul_nonneg (hε r hr) hquad) hden.le
  have hsum :
      ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
        = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r +
            ∑ r ∈ N, A r * entropyProduction r := by
    simp_rw [mul_add, mul_neg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  calc
    dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r
        = (1 / V) * ∑ r ∈ N, A r * entropyProduction r := by
          rw [hd, hsum]
          ring
    _ ≥ 0 := by
      exact mul_nonneg (one_div_nonneg.mpr hV.le)
        (Finset.sum_nonneg (fun r hr => mul_nonneg (hA r hr) (hprod r hr)))
