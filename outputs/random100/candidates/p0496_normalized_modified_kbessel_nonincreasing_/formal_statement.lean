theorem normalized_modified_kBessel_nonincreasing_logConvex
    (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    let Γk : ℝ → ℝ := fun z => k ^ (z / k - 1) * Real.Gamma (z / k)
    let 𝓘 : ℝ → ℝ := fun ν => ∑' r : ℕ,
      Γk (ν + k) /
        (Γk ((r : ℝ) * k + ν + k) * (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧
      (∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 →
        𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)) := by sorry
