theorem paired_complex_tuple_set_convex
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (σ : Fin (l + m) → Fin (l + m))
    (hσ_involutive : Function.Involutive σ)
    (hσ_fixedPointFree : ∀ i, σ i ≠ i) :
    Convex ℝ {ζ : Fin (l + m) → ℂ |
      (∀ i, ζ i = ζ (σ i)) ∧
      (∀ i, 0 < (ζ i).re) ∧
      (∀ i : ℕ, 1 ≤ i → i < l →
        0 < (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < i), ζ k).im) ∧
      (∀ j : ℕ, 1 ≤ j → j < m →
        (∑ k ∈ Finset.univ.filter
          (fun k : Fin (l + m) => l ≤ k.val ∧ k.val < l + j), ζ k).im < 0) ∧
      (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k} := by sorry
