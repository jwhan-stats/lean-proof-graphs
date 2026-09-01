theorem diagonal_nonnegative_part_difference
    (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
    let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
    ∃ ω : Fin n → ℝ,
      (∀ i, 0 ≤ ω i ∧ ω i ≤ 1) ∧
        Matrix.mulVec (P x) x - Matrix.mulVec (P y) y =
          Matrix.mulVec (Matrix.diagonal ω) (x - y) := by sorry
