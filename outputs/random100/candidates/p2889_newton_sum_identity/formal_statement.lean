theorem newton_sum_identity
    {K : Type*} [Field K] (d : ℕ) (ξ : ℕ → K)
    (hξ : Set.InjOn ξ (Set.Icc 0 d)) :
    ∑ i ∈ Finset.range (d + 1),
        (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) *
          Polynomial.C ((∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹) =
      (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) *
        Polynomial.C ((∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹) := by sorry
