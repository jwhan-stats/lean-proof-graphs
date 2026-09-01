theorem approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    {w : ℂ |
        ∃ x : ℕ → H,
          (∀ n : ℕ, ‖x n‖ = 1) ∧
            Filter.Tendsto (fun n : ℕ => ‖T (x n) - w • x n‖)
              Filter.atTop (nhds 0)} ⊆
      closure
        {z : ℂ |
          ∃ x : H, ‖x‖ = 1 ∧
            let a : ℝ := (inner ℂ (T x) x).re
            let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
            z = (a : ℂ) + Complex.I * (b : ℂ) ∨
              z = (a : ℂ) - Complex.I * (b : ℂ)} := by sorry
