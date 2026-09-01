theorem no_implementing_star_hom
    {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (α : A →⋆ₙₐ[ℂ] A)
    (hα : α 1 = 1)
    (hessential : ∀ a : A,
      (∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α, a * (x : A) = 0) → a = 0) :
    let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
    letI : ContinuousStar I :=
      ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
    let B := A × ZeroAtInftyContinuousMap ℕ I
    ¬ ∃ β : B →⋆ₙₐ[ℂ] B, ∀ b b' : B,
      (β b * b').1 = α b.1 * b'.1 ∧
      (↑((β b * b').2 0) : A) = α b.1 * ↑(b'.2 0) ∧
      ∀ n : ℕ, (↑((β b * b').2 (n + 1)) : A) =
        (↑(b.2 n) : A) * ↑(b'.2 (n + 1)) := by sorry
