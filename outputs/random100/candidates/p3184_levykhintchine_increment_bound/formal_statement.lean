theorem levyKhintchine_increment_bound
    (b σ2 Δ : ℝ) (n : ℝ → NNReal)
    (hσ2 : 0 ≤ σ2) (hΔ : 0 ≤ Δ)
    (hn : Measurable n)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) :
    let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
    let hstar : ℝ → ℂ := fun v =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
    let ψΔ : ℝ → ℂ := fun u =>
      Complex.exp ((Δ : ℂ) *
        (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
          ∫ x : ℝ,
            (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
              Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)))
    let c : ℝ → ℝ := fun u =>
      |b| + ∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖
    (∀ u : ℝ, ‖ψΔ u - 1‖ ≤ Δ * |u| * (c u + σ2 * |u|)) ∧
      (MeasureTheory.Integrable hstar →
        ∀ u : ℝ,
          ‖ψΔ u - 1‖ ≤
            Δ * |u| * (|b| + (∫ v : ℝ, ‖hstar v‖) + σ2 * |u|)) := by sorry
