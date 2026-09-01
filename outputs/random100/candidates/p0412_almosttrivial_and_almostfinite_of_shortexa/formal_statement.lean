theorem almostTrivial_and_almostFinite_of_shortExact
    {R : Type*} [CommRing R] [IsDomain R]
    {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    ((∃ r : R, r ≠ 0 ∧ ∀ m : M₁, r • m = 0) ↔
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₀, r • m = 0) ∧
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₂, r • m = 0)) ∧
    (IsNoetherianRing R →
      (((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) ∧
          Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)) ↔
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0) ∧
          Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) ∧
          Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))) := by sorry
