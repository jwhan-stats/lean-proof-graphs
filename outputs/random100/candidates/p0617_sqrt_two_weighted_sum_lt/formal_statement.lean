theorem sqrt_two_weighted_sum_lt (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), ((i - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j) <
      (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i := by sorry
