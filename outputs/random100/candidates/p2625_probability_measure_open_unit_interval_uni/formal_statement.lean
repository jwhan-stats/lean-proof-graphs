theorem probability_measure_open_unit_interval_unique_solution
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ s : ℝ,
      0 < s ∧
        s < 1 ∧
          (∫ x, (Real.exp (s * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 ∧
            ∀ t : ℝ,
              0 < t →
                (∫ x, (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 →
                  t = s := by sorry
