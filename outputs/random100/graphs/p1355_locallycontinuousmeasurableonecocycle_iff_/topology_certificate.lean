import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1355_locallycontinuousmeasurableonecocycle_iff_
-- topology_sha256: eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b
namespace TopologyCertificate_p1355_locallycontinuousmeasurableonecocycle_iff

-- N001 = inst._@.proofs.1843747912._hygCtx._hyg.10: IsTopologicalGroup G
-- N002 = inst._@.proofs.1843747912._hygCtx._hyg.26: ContinuousSMul G A
-- N003 = inst._@.proofs.1843747912._hygCtx._hyg.39: BorelSpace A
-- N004 = inst._@.proofs.1843747912._hygCtx._hyg.19: IsTopologicalAddGroup A
-- N005 = inst._@.proofs.1843747912._hygCtx._hyg.33: BorelSpace G
-- N006 = goal: (Measurable c ∧ (∀ (s t : G), c (s * t) = c s + s • c t) ∧ ∃ U, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn c U) ↔ Continuous c ∧ ∀ (s t : G), c (s * t) = c s + s • c t

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N001 → N004 → N002 → N005 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B001 B004 B002 B005 B003
  exact H_N006

end TopologyCertificate_p1355_locallycontinuousmeasurableonecocycle_iff
