import Mathlib

/- verified submission -/
theorem exists_coloring_increasing_pairs :
    ∃ c : ℕ × ℕ → ℕ,
      (∀ n m : ℕ, n < m → c (n, m) < m) ∧
      ∀ n k : ℕ, ∀ B : Set ℕ, B.Infinite →
        ∃ m ∈ B, n < m ∧ k ≤ c (n, m) := by
  use fun p => p.2 - 1
  constructor
  · intro n m h
    show m - 1 < m
    omega
  · intro n k B hB
    obtain ⟨m, hmB, hm⟩ := hB.exists_gt (max n k)
    refine ⟨m, hmB, lt_of_le_of_lt (Nat.le_max_left n k) hm, ?_⟩
    show k ≤ m - 1
    have := Nat.le_max_right n k
    omega
