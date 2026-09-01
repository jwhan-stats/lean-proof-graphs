import Mathlib

/- verified submission -/
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
    h = Homeomorph.refl E := by
  apply Homeomorph.ext
  intro x
  let γ : Path e x := PathConnectedSpace.somePath e x
  let f : C(Set.Icc (0 : ℝ) 1, B) := ⟨fun t => p (γ t), hp.comp γ.continuous⟩
  let g₁ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => γ t, γ.continuous⟩
  let g₂ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => h (γ t), h.continuous.comp γ.continuous⟩
  have hbase : p e = f 0 := by
    exact (congrArg p γ.source).symm
  have huniq := arc_lifting f 0 e hbase
  have hg₁ : (∀ t, p (g₁ t) = f t) ∧ g₁ 0 = e := by
    constructor
    · intro t
      rfl
    · exact γ.source
  have hg₂ : (∀ t, p (g₂ t) = f t) ∧ g₂ 0 = e := by
    constructor
    · intro t
      exact congrFun hdeck (γ t)
    · calc
        g₂ 0 = h (γ 0) := rfl
        _ = h e := congrArg h γ.source
        _ = e := he
  have hg : g₁ = g₂ := huniq.unique hg₁ hg₂
  have hx : γ 1 = h (γ 1) := congrArg (fun g : C(Set.Icc (0 : ℝ) 1, E) => g 1) hg
  calc
    h x = h (γ 1) := by rw [γ.target]
    _ = γ 1 := hx.symm
    _ = x := γ.target
