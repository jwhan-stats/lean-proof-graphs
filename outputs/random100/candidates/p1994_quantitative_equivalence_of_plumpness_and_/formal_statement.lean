theorem quantitative_equivalence_of_plumpness_and_dyadic_plumpness
    {X : Type*} [MetricSpace X] (E : Set X) :
    (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
      (∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) →
      ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
        0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
        b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R →
        ∀ y ∈ E, ∀ k : ℤ, m ≤ k →
          ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
            Metric.ball y (B₀ * δ ^ k) ∩ E) ∧
    (∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
      0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
      (∀ y ∈ E, ∀ k : ℤ, m ≤ k →
        ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
          Metric.ball y (B₀ * δ ^ k) ∩ E) →
      ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
        b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) →
        ∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
          ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) := by sorry
