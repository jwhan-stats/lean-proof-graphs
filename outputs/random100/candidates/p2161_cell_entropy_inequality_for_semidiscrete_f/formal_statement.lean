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
        (1 / V) * ∑ r ∈ N, A r * g r ≥ 0 := by sorry
