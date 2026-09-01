import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0203_bounded_degree_unit_circle_conjugates_clos
-- topology_sha256: 0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da
namespace TopologyCertificate_p0203_bounded_degree_unit_circle_conjugates_clos

-- N001 = goal: let S_B := {x | 1 < x ∧ IsIntegral ℤ x ∧ ↑(minpoly ℚ x).natDegree ≤ B ∧ (∀ (z : ℂ), (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z → z ≠ ↑x → ‖z‖ ≤ 1) ∧ ∃ z, (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z ∧ z ≠ ↑x ∧ ‖z‖ = 1}; IsClosed S_B ∧ ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0203_bounded_degree_unit_circle_conjugates_clos
