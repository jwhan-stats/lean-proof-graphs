theorem reverse_cauchy_schwarz_with_three_term_min
    (n : ℕ) (hn : 1 ≤ n)
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    ((∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2))
          (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2))
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)))) ∧
    (∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j)) := by sorry
