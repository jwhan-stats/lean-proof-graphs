theorem lebesgue_integral_modified_salem
    (p₀ p₁ p₂ : ℝ)
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    let p : Fin 3 → ℝ := ![p₀, p₁, p₂]
    let β : Fin 3 → ℝ := ![0, p₀, p₀ + p₁]
    let E : (ℕ → Fin 3) → ℝ := fun i ↦
      ∑' k : ℕ, β (i k) * ∏ r ∈ Finset.range k, p (i r)
    let canonical : ℝ → (ℕ → Fin 3) := fun x ↦
      Classical.epsilon fun i ↦
        E i = x ∧
          ((∃ j, E j = x ∧ j ≠ i) →
            ∃ N, ∀ k, N ≤ k → i k = 0)
    let θ : Fin 3 → Fin 3 := ![0, 2, 1]
    let f : ℝ → ℝ := fun x ↦ E (fun k ↦ θ (canonical x k))
    MeasureTheory.IntegrableOn f (Set.Icc 0 1) ∧
      (∫ x in (0 : ℝ)..1, f x) =
        (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
          (1 - p₀ ^ 2 - 2 * p₁ * p₂) := by sorry
