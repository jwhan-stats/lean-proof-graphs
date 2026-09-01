theorem proposition_4_9
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ))))) :
    (∫⁻ x, ∫⁻ y,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ ∂μ) < ⊤ := by sorry
