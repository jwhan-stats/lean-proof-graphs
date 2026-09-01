theorem matrix_kronecker_injective_iff_linearIndependent
    (g d e : ℕ) (hg : 0 < g) (hd : 0 < d) (he : 0 < e)
    (A : Fin g → Matrix (Fin d) (Fin e) ℂ) :
    let c₁ : Prop := ∀ (n : ℕ), 0 < n → ∀ X : Fin g → Matrix (Fin n) (Fin n) ℂ,
      (∑ j, Matrix.kronecker (A j) (X j)) = 0 → ∀ j, X j = 0
    let c₂ : Prop := ∀ z : Fin g → ℂ,
      (∑ j, z j • A j) = 0 → ∀ j, z j = 0
    let c₃ : Prop := LinearIndependent ℂ A
    (c₁ ↔ c₂) ∧ (c₂ ↔ c₃) := by sorry
