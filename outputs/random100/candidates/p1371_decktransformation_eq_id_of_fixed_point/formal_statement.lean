theorem deckTransformation_eq_id_of_fixed_point
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E]
    (p : E → B) (hp : Continuous p)
    (arc_lifting : ∀ (f : C(Set.Icc (0 : ℝ) 1, B))
      (t₀ : Set.Icc (0 : ℝ) 1) (e₀ : E), p e₀ = f t₀ →
        ∃! g : C(Set.Icc (0 : ℝ) 1, E),
          (∀ t, p (g t) = f t) ∧ g t₀ = e₀)
    (h : E ≃ₜ E) (hdeck : p ∘ h = p)
    {e : E} (he : h e = e) :
    h = Homeomorph.refl E := by sorry
