theorem two_local_inner_derivation_matrix_is_inner
    (R : Type*) [CommRing R] (n : ℕ) (hn : 1 < n)
    (h2 : IsUnit (2 : R))
    (Δ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)
    (hΔ : ∀ X Y, ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A) :
    ∃ B, ∀ X, Δ X = B * X - X * B := by sorry
