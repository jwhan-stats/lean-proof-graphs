import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3114_dimension_three_evaluation_of_asymptotic_c
-- topology_sha256: f3ac9afe8a0768f21a7fcd2874352f2bb2ead0abe5b84fdd5a46b71d0f19fc12
namespace TopologyCertificate_p3114_dimension_three_evaluation_of_asymptotic_c

-- N001 = goal: let H := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1; let arccot := fun a => Real.pi / 2 - Real.arctan a; let κ := fun a => 1 / (4 * Real.pi) * ((-(1 / (2 * Real.pi)) * ∫ (η : ℝ) in -1..1, if a = 0 ∧ η = 0 then 0 else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) - 1 / 4 + H a * (1 + a ^ 2)); ∀ (a : ℝ), κ a = 1 / (4 * Real.pi) * (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi + (1 + a ^ 2) + a / Real.pi)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p3114_dimension_three_evaluation_of_asymptotic_c
