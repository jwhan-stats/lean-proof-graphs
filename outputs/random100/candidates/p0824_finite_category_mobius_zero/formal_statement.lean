theorem finite_category_mobius_zero
    {A : Type u} [CategoryTheory.Category.{v, u} A] [Fintype A]
    [DecidableEq A] [∀ a b : A, Fintype (a ⟶ b)]
    (μ : A → A → ℚ)
    (hμζ : ∀ a c : A,
      ∑ b : A, μ a b * (Fintype.card (b ⟶ c) : ℚ) =
        if a = c then 1 else 0)
    (hζμ : ∀ a c : A,
      ∑ b : A, (Fintype.card (a ⟶ b) : ℚ) * μ b c =
        if a = c then 1 else 0)
    {a b : A} (hab : IsEmpty (a ⟶ b)) :
    μ a b = 0 := by sorry
