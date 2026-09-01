import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1462_locallycompact_prod_ascoli
-- topology_sha256: 2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f
namespace TopologyCertificate_p1462_locallycompact_prod_ascoli

-- N001 = hK: IsCompact K
-- N002 = hX: ∀ (K : Set C(X, ℝ)), IsCompact K → Continuous fun p => ↑p.1 p.2
-- N003 = inst._@.proofs.2729584061._hygCtx._hyg.10: LocallyCompactSpace Z
-- N004 = hΦ: Continuous Φ
-- N005 = goal: Continuous fun p => ↑p.1 p.2

-- E001 represents h_001_h
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N004)
    (E002 : N003 → N002 → N001 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B003
  have H_N005 : N005 := E002 B003 B002 B001 H_N004
  exact H_N005

end TopologyCertificate_p1462_locallycompact_prod_ascoli
