theorem scaling_implies_a_cone_distance
    {C X : Type*} [MetricSpace C]
    (q : X × NNReal → C)
    (hq : Function.Surjective q)
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4) :
    let d_X : X × X → ℝ := fun p =>
      Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2);
    (∀ x₀ x₁ : X, d_X (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
      (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
        @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = d_X (x₀, x₁)) ∧
      ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
        dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
          (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
            2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (d_X (x₀, x₁)) := by sorry
