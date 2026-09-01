import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1776_subgroup_isup_eq_boolean_isup
-- topology_sha256: fb662cf9564d5c688def1900e978d2b19b77ef282febb3dedb4a33e5a1159239
namespace TopologyCertificate_p1776_subgroup_isup_eq_boolean_isup

-- N001 = hgen: AddSubgroup.closure (Set.range a) = ⊤
-- N002 = hprod: ∀ (x y : A), ↑(W x) ⊆ Set.image2 (fun g h => g * h) ↑(W y) ↑(W (2 • y - x))
-- N003 = goal: ⨆ x, W x = ⨆ s, W (∑ i ∈ s, a i)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p1776_subgroup_isup_eq_boolean_isup
