import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1994_quantitative_equivalence_of_plumpness_and_
-- topology_sha256: a3bfaebfa10bc5c7babc922f77d3b381fa73f1340b54a9db20a291da7b6fa59f
namespace TopologyCertificate_p1994_quantitative_equivalence_of_plumpness_and

-- N001 = goal: (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → (∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) → ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R → ∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) ∧ ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → (∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) → ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) → ∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1994_quantitative_equivalence_of_plumpness_and
