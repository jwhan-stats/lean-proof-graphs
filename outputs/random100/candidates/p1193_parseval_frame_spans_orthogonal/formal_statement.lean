theorem parseval_frame_spans_orthogonal
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2)
    (I : Set (Fin N))
    (hdisjoint : Submodule.span ℝ (φ '' I) ⊓
      Submodule.span ℝ (φ '' Iᶜ) = ⊥) :
    ∀ u ∈ Submodule.span ℝ (φ '' I),
      ∀ v ∈ Submodule.span ℝ (φ '' Iᶜ), inner ℝ u v = 0 := by sorry
