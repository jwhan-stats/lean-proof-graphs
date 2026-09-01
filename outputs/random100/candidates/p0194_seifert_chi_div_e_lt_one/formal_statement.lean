theorem seifert_chi_div_e_lt_one
    (t d : ℕ) (n q : ℕ → ℕ)
    (hn : ∀ i, 1 ≤ i → i ≤ t → 2 ≤ n i)
    (hq_pos : ∀ i, 1 ≤ i → i ≤ t → 1 ≤ q i)
    (hq_lt : ∀ i, 1 ≤ i → i ≤ t → q i < n i)
    (hcoprime : ∀ i, 1 ≤ i → i ≤ t → Nat.Coprime (n i) (q i))
    (he : 0 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ))
    (hcases :
      (t = 3 ∧
        (4 ≤ d ∨
          (d = 3 ∧ q 1 = 1) ∨
          (d = 2 ∧ q 1 = 1 ∧ q 2 = 1))) ∨
      (t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1)) :
    let e : ℚ := (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ)
    let χ : ℚ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / (n i : ℚ))
    χ / e < 1 := by sorry
