theorem simple_selection_adjusted_control
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (hP_independent : ProbabilityTheory.iIndepFun P μ)
    (S : ((i : Fin m) → (Fin (n i) → Set.Icc (0 : ℝ) 1)) → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_countable : (Set.range
      (fun z : Σ i : Fin m, ℝ × (Fin (n i) → Set.Icc (0 : ℝ) 1) =>
        C z.1 z.2.1 z.2.2)).Countable)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α) :
    ∫ ω,
      if (S (fun i => P i ω)).card = 0 then 0
      else
        (∑ i ∈ S (fun j => P j ω),
          C i (((S (fun j => P j ω)).card : ℝ) * q / (m : ℝ)) (P i ω)) /
          ((S (fun i => P i ω)).card : ℝ) ∂μ ≤ q := by sorry
