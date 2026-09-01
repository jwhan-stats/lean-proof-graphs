theorem unique_nonzero_zero_of_exponential_factorial_sum
    (n k : ℕ) (hn : 2 ≤ n) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    let h : ℝ → ℝ := fun x ↦
      Real.exp (2 * (k : ℝ) * x) *
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) + (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) + (k : ℝ) - (j : ℝ)) * x ^ j)
        - (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) - (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) - (k : ℝ) - (j : ℝ)) * x ^ j)
    ∃ c : ℝ, -1 < c ∧ c < 0 ∧ h c = 0 ∧
      ∀ x : ℝ, h x = 0 ↔ x = 0 ∨ x = c := by sorry
