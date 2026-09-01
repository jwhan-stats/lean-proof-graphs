import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2889_newton_sum_identity
-- topology_sha256: 86a1e5f723ab4767e2f23767e35423d77febdd24a773f42fe5a06af671650480
namespace TopologyCertificate_p2889_newton_sum_identity

-- N001 = hξ: Set.InjOn ξ (Set.Icc 0 d)
-- N002 = goal: ∑ i ∈ Finset.range (d + 1), (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹ = (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p2889_newton_sum_identity
