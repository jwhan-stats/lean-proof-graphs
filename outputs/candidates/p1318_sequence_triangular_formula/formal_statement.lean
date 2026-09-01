theorem sequence_triangular_formula
    (c : ℕ → ℕ)
    (hc₁ : c 1 = 2)
    (hc : ∀ k : ℕ, 0 < k →
      c (2 * k) = 2 * (k + 1) ^ 2 ∧
      c (2 * k + 1) = 2 * (k + 1) ^ 2) :
    ∀ n : ℕ, 0 < n →
      let m := (n + 2) / 2
      let t : ℕ → ℕ := fun r => r * (r + 1) / 2
      c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m) := by sorry
