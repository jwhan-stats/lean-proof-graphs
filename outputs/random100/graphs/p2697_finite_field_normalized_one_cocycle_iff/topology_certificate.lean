import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2697_finite_field_normalized_one_cocycle_iff
-- topology_sha256: 4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151
namespace TopologyCertificate_p2697_finite_field_normalized_one_cocycle_iff

-- N001 = hα: α ≠ 0
-- N002 = hν: orderOf ν = q
-- N003 = inst._@.proofs.2502934680._hygCtx._hyg.11: Fact (Nat.Prime q)
-- N004 = inst._@.proofs.2502934680._hygCtx._hyg.8: Fact (Nat.Prime p)
-- N005 = goal: (α 0 = 0 ∧ ∀ (x y : ZMod q), α (x + y) = α x + (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ x.val * α y) ↔ ∃ r, r ≠ 0 ∧ α 0 = 0 ∧ ∀ (x : ZMod q), x ≠ 0 → α x = r * ∑ j ∈ Finset.range x.val, (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ j

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
    (E001 : N004 → N003 → N002 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B002 B001
  exact H_N005

end TopologyCertificate_p2697_finite_field_normalized_one_cocycle_iff
