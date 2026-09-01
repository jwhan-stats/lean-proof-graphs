theorem exists_coloring_increasing_pairs :
    ∃ c : ℕ × ℕ → ℕ,
      (∀ n m : ℕ, n < m → c (n, m) < m) ∧
      ∀ n k : ℕ, ∀ B : Set ℕ, B.Infinite →
        ∃ m ∈ B, n < m ∧ k ≤ c (n, m) := by sorry
