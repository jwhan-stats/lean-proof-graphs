import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2753_planeposet_union_islinearorder
-- topology_sha256: 3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397
namespace TopologyCertificate_p2753_planeposet_union_islinearorder

-- N001 = hcompat: ∀ {x y : P}, x ≠ y → (leH x y ∨ leH y x ↔ ¬(leR x y ∨ leR y x))
-- N002 = hH: IsPartialOrder P leH
-- N003 = hR: IsPartialOrder P leR
-- N004 = goal: IsLinearOrder P fun x y => leH x y ∨ leR x y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2753_planeposet_union_islinearorder
