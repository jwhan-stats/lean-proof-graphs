theorem euclidean_decomposition_bound (n e p : ℕ) (hn : 0 < n) (he : 0 < e)
    (hp : Nat.Prime p) (hsize : 4 * p ^ 2 ≤ n + 2) (hep : e ≤ p + 1) :
    ∃ d f : ℕ, f < p ∧ n + 2 = p * d + f + e ∧
      d ≥ e + f + (2 * p - 2) := by sorry
