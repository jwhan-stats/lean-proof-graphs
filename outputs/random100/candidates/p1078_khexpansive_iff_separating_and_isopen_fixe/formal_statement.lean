theorem khExpansive_iff_separating_and_isOpen_fixedPoints
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))) :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 →
        ((∀ t : ℝ, dist (φ (t, x)) (φ (s t, x)) < δ) ∧
          (∀ t : ℝ, dist (φ (t, x)) (φ (s t, y)) < δ)) →
        y ∈ Set.range (fun t : ℝ => φ (t, x))) ↔
      ((∃ α : ℝ, 0 < α ∧
        ∀ x y : Λ,
          (∀ t : ℝ, dist (φ (t, x)) (φ (t, y)) < α) →
          y ∈ Set.range (fun t : ℝ => φ (t, x))) ∧
        IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) := by sorry
