theorem bounded_degree_unit_circle_conjugates_closed_discrete
    (B : ℝ) (hB : 0 < B) :
    let S_B : Set ℝ :=
      {x | 1 < x ∧
        IsIntegral ℤ x ∧
        ((minpoly ℚ x).natDegree : ℝ) ≤ B ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z ∧
          z ≠ (x : ℂ) ∧ ‖z‖ = 1)};
    IsClosed S_B ∧
      ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x} := by sorry
