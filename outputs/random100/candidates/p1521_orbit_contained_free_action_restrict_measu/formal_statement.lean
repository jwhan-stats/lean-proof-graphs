theorem orbit_contained_free_action_restrict_measure_preserving
    {Γ Δ Y : Type*} [Group Γ] [Group Δ] [Countable Γ] [Countable Δ]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MulAction Γ Y] [MulAction Δ Y]
    [MeasurableConstSMul Γ Y] [MeasurableConstSMul Δ Y]
    (hc_free : ∀ y : Y, MulAction.stabilizer Γ y = ⊥)
    (hd_free : ∀ y : Y, MulAction.stabilizer Δ y = ⊥)
    (horbit : ∀ (δ : Δ) (y : Y), ∃ γ : Γ, δ • y = γ • y)
    (A : Set Y) (hA_meas : MeasurableSet A)
    (hA_inv : ∀ δ : Δ, (fun y : Y => δ • y) '' A = A)
    (μ : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.SMulInvariantMeasure Γ Y μ]
    (hμA : μ A = 1) :
    ∀ (δ : Δ) (B : Set Y), MeasurableSet B → B ⊆ A →
      μ ((fun y : Y => δ • y) '' B) = μ B := by sorry
