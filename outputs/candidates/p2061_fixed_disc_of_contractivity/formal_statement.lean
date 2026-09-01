theorem fixed_disc_of_contractivity
    {X : Type*} [MetricSpace X]
    (T : X → X) (x₀ : X) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hcontractive : ∀ x : X, dist (T x) x ≤ c * dist (T x) x₀) :
    let ρ : ℝ := sInf {r : ℝ | ∃ x : X, T x ≠ x ∧ r = dist x (T x)}
    (∀ x : X, dist x x₀ ≤ ρ → x ≠ x₀ →
      0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) →
    ∀ x : X, dist x x₀ ≤ ρ → T x = x := by sorry
