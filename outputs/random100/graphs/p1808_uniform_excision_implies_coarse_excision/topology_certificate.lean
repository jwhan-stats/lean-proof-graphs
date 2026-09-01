import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1808_uniform_excision_implies_coarse_excision
-- topology_sha256: 9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee
namespace TopologyCertificate_p1808_uniform_excision_implies_coarse_excision

-- N001 = hAB: A ∪ B = Set.univ
-- N002 = hcompat: ∃ E ∈ uniformity X, E ∈ coarse
-- N003 = hex: ∃ U ∈ uniformity X, ∃ κ, Monotone κ ∧ (∀ V ∈ uniformity X, ∃ W, ↑W ∈ uniformity X ∧ OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧ ∀ (W : { W // W ⊆ U }), (↑W).image A ∩ (↑W).image B ⊆ (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B)
-- N004 = hV: V ∈ coarse
-- N005 = goal: ∃ T ∈ coarse, V.image A ∩ V.image B ⊆ T.image (A ∩ B)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N002 → N003 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B001 B002 B003 B004
  exact H_N005

end TopologyCertificate_p1808_uniform_excision_implies_coarse_excision
