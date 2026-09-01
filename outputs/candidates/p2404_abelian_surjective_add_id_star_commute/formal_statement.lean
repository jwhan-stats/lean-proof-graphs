theorem abelian_surjective_add_id_star_commute
    {A : Type*} [AddCommGroup A] (φ : A →+ A)
    (hφ : Function.Surjective φ) :
    let ψ : A → A := fun a ↦ φ a + a
    Function.Commute φ ψ ∧
      ∀ x y : A, ψ x = φ y → ∃! z : A, φ z = x ∧ ψ z = y := by sorry
