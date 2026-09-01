theorem antitone_monotone_power_sum_inequality
    (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 1 ≤ s)
    (a b : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i)
    (ha_antitone : Antitone a)
    (hb_monotone : Monotone b) :
    (∑ i : Fin k, Real.rpow (a i) s) * (∑ i : Fin k, (a i) ^ 2 * b i) ≤
      (∑ i : Fin k, Real.rpow (a i) (s + 1)) * (∑ i : Fin k, a i * b i) := by sorry
