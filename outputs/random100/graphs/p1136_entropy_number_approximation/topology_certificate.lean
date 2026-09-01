import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1136_entropy_number_approximation
-- topology_sha256: 35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704
namespace TopologyCertificate_p1136_entropy_number_approximation

-- N001 = hn: 0 < n
-- N002 = goal: let e := fun k T => ⨅ ε, ⨅ (_ : 0 < ε), ⨅ (_ : Metric.externalCoveringNumber ε (⇑T '' Metric.closedBall 0 1) ≤ 2 ^ (k - 1)), ↑ε; e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (⨆ γ, e n (Vγ γ)) + ⨆ x, ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ, ENNReal.ofReal ‖V x - (Vγ γ) x‖

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p1136_entropy_number_approximation
