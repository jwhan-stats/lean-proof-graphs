theorem logarithmic_average_bound
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun N c ↦
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let Lℂ : ({n : ℕ // 0 < n} → ℂ) → ℂ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℂ)) / (∑ m ∈ B, 1 / (m.1 : ℂ))
    let Lℝ : ({n : ℕ // 0 < n} → ℝ) → ℝ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℝ)) / (∑ m ∈ B, 1 / (m.1 : ℝ))
    Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤
      Real.sqrt (Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))) := by sorry
