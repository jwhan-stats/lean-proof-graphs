theorem strongMetricEnvelopeOfHeight
    {G : Type*} [CommGroup G] (ρ : G → ℝ)
    (hρ_lower : ∀ α : G, 1 ≤ ρ α)
    (hρ_one : ρ 1 = 1)
    (hρ_inv : ∀ α : G, ρ α⁻¹ = ρ α) :
    let envelopeOne : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        (∏ᶠ n, f (a n)) = r}
    let envelopeInf : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}
    ((∀ α : G, 1 ≤ envelopeInf ρ α) ∧
      envelopeInf ρ 1 = 1 ∧
      (∀ α : G, envelopeInf ρ α⁻¹ = envelopeInf ρ α) ∧
      (∀ α β : G,
        envelopeInf ρ (α * β) ≤ max (envelopeInf ρ α) (envelopeInf ρ β))) ∧
    (∀ α : G, envelopeInf ρ α ≤ envelopeOne ρ α) ∧
    (∀ σ : G → ℝ,
      ((∀ α : G, 1 ≤ σ α) ∧
        σ 1 = 1 ∧
        (∀ α : G, σ α⁻¹ = σ α) ∧
        (∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))) →
      (∀ α : G, σ α ≤ ρ α) →
      ∀ α : G, σ α ≤ envelopeInf ρ α) ∧
    (ρ = envelopeInf ρ ↔
      (∀ α : G, 1 ≤ ρ α) ∧
      ρ 1 = 1 ∧
      (∀ α : G, ρ α⁻¹ = ρ α) ∧
      (∀ α β : G, ρ (α * β) ≤ max (ρ α) (ρ β))) ∧
    (envelopeInf ρ = envelopeInf (envelopeOne ρ) ∧
      envelopeInf (envelopeOne ρ) = envelopeOne (envelopeInf ρ) ∧
      envelopeOne (envelopeInf ρ) = envelopeInf (envelopeInf ρ)) := by sorry
