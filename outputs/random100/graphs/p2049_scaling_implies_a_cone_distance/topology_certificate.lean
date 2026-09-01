import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2049_scaling_implies_a_cone_distance
-- topology_sha256: 5e7d1222eab3158d1cbc4ea284d43f37ff4452b5d3b0f9afe6796516f43e5058
namespace TopologyCertificate_p2049_scaling_implies_a_cone_distance

-- N001 = hbound: ∀ (x₀ x₁ : X), x₀ ≠ x₁ → 0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧ dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4
-- N002 = hscale: ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ * ↑r₁ * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 + (↑r₀ - ↑r₁) ^ 2
-- N003 = goal: let d_X := fun p => Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2); (∀ (x₀ x₁ : X), d_X (x₀, x₁) ∈ Set.Icc 0 Real.pi) ∧ (∃ m, ∀ (x₀ x₁ : X), dist x₀ x₁ = d_X (x₀, x₁)) ∧ ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ ^ 2 + ↑r₁ ^ 2 - 2 * ↑r₀ * ↑r₁ * Real.cos (d_X (x₀, x₁))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B002 B001
  exact H_N003

end TopologyCertificate_p2049_scaling_implies_a_cone_distance
