theorem proposition_3_8 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    let κ : (m : ℕ) → Nat.Partition m → Polynomial ℤ := fun _ ρ =>
      if ρ.parts.Nodup then
        (-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card
      else 0
    let ε : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
            ∏ i, κ (s i : ℕ) (p i)
        else 0
    let pp : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
            (1 - Polynomial.X : Polynomial ℤ) ^
              (∑ i, (ρ i).parts.toFinset.card)
        else 0
    let ε₁ : ℕ → ℤ := fun a => Polynomial.eval 1 (ε a)
    ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r) := by sorry
