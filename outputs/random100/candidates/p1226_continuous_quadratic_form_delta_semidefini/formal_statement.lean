theorem continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (hq : ∃ b : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q x = b x x)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x) :
    ((∃ q₁ q₂ : X → ℝ,
        (∃ b₁ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₁ x = b₁ x x) ∧
        (∃ b₂ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₂ x = b₂ x x) ∧
        (∀ x : X, 0 ≤ q₁ x) ∧
        (∀ x : X, 0 ≤ q₂ x) ∧
        (∀ x : X, q x = q₁ x - q₂ x)) ↔
      (∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x))) ∧
    ((∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x)) ↔
      (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
        T = B.comp A)) := by sorry
