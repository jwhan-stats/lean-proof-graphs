theorem average_projection_positive_definite
    {n : ℕ} (hn : 1 ≤ n)
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (C : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hC : ⨆ i, C i = ⊤)
    (J : Ω → Finset ι)
    (hproj : Measurable (fun ω =>
      (∑ i ∈ J ω, C i).starProjection))
    (hadm : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1) :
    ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < inner ℝ x
        ((∫ ω, (∑ i ∈ J ω, C i).starProjection ∂μ) x) := by sorry
