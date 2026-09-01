import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1572_not_biorderable_of_product_conjugates_eq_o
-- topology_sha256: 5ada9e25b8527e7bb3ae0d80bab4d4a3d543f5311c77d5c36a9536ad537bc67f
namespace TopologyCertificate_p1572_not_biorderable_of_product_conjugates_eq_o

-- N001 = a._@._internal.0.proofs.1064056188._hygCtx._hyg.161: ∃ r, IsStrictTotalOrder G r ∧ (∀ (a b c : G), r a b ↔ r (c * a) (c * b)) ∧ ∀ (a b c : G), r a b ↔ r (a * c) (b * c)
-- N002 = h: ∃ g k x, g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn fun i => (x i)⁻¹ * g * x i).prod = 1
-- N003 = goal: False

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

end TopologyCertificate_p1572_not_biorderable_of_product_conjugates_eq_o
