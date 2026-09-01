theorem two_positive_roots_of_mu
    (n : ℤ) (hn : 4 ≤ n)
    (M Λ : ℝ) (hM : 0 < M) (hΛ : 0 < Λ) :
    let lam : ℝ := 2 * Λ / (((n : ℝ) - 2) * ((n : ℝ) - 1))
    let mu : ℝ → ℝ := fun r ↦ 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2
    M ^ 2 * lam ^ (n - 3) <
        ((n : ℝ) - 3) ^ (n - 3) / ((n : ℝ) - 1) ^ (n - 1) →
      ∃ r_minus r_plus : ℝ,
        0 < r_minus ∧ r_minus < r_plus ∧
        mu r_minus = 0 ∧ mu r_plus = 0 ∧
        ∀ r : ℝ, 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus := by sorry
